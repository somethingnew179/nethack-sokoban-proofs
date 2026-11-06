import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1329_0_checked : (List.range' 680448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1329_1_checked : (List.range' 680576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1329_2_checked : (List.range' 680704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1329_3_checked : (List.range' 680832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1329_range (index : Nat) (lower : 680448 ≤ index) (upper : index < 680960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 680704 then
    if cut : index < 680576 then
      exact segment_sound _ 680448 128 Restriction1329_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 680576 128 Restriction1329_1_checked index (by omega) (by omega)
  else
    if cut : index < 680832 then
      exact segment_sound _ 680704 128 Restriction1329_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 680832 128 Restriction1329_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
