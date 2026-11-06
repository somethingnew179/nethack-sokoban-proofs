import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1142_0_checked : (List.range' 584704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1142_1_checked : (List.range' 584832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1142_2_checked : (List.range' 584960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1142_3_checked : (List.range' 585088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1142_range (index : Nat) (lower : 584704 ≤ index) (upper : index < 585216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 584960 then
    if cut : index < 584832 then
      exact segment_sound _ 584704 128 Restriction1142_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 584832 128 Restriction1142_1_checked index (by omega) (by omega)
  else
    if cut : index < 585088 then
      exact segment_sound _ 584960 128 Restriction1142_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 585088 128 Restriction1142_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
