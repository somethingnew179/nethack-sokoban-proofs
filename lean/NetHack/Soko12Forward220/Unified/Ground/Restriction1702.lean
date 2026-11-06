import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1702_0_checked : (List.range' 871424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1702_1_checked : (List.range' 871552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1702_2_checked : (List.range' 871680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1702_3_checked : (List.range' 871808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1702_range (index : Nat) (lower : 871424 ≤ index) (upper : index < 871936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 871680 then
    if cut : index < 871552 then
      exact segment_sound _ 871424 128 Restriction1702_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 871552 128 Restriction1702_1_checked index (by omega) (by omega)
  else
    if cut : index < 871808 then
      exact segment_sound _ 871680 128 Restriction1702_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 871808 128 Restriction1702_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
