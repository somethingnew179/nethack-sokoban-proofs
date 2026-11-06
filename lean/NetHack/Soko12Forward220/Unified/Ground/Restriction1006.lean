import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1006_0_checked : (List.range' 515072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1006_1_checked : (List.range' 515200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1006_2_checked : (List.range' 515328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1006_3_checked : (List.range' 515456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1006_range (index : Nat) (lower : 515072 ≤ index) (upper : index < 515584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 515328 then
    if cut : index < 515200 then
      exact segment_sound _ 515072 128 Restriction1006_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 515200 128 Restriction1006_1_checked index (by omega) (by omega)
  else
    if cut : index < 515456 then
      exact segment_sound _ 515328 128 Restriction1006_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 515456 128 Restriction1006_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
