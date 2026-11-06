import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1017_0_checked : (List.range' 520704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1017_1_checked : (List.range' 520832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1017_2_checked : (List.range' 520960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1017_3_checked : (List.range' 521088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1017_range (index : Nat) (lower : 520704 ≤ index) (upper : index < 521216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 520960 then
    if cut : index < 520832 then
      exact segment_sound _ 520704 128 Restriction1017_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 520832 128 Restriction1017_1_checked index (by omega) (by omega)
  else
    if cut : index < 521088 then
      exact segment_sound _ 520960 128 Restriction1017_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 521088 128 Restriction1017_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
