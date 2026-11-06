import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1239_0_checked : (List.range' 634368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1239_1_checked : (List.range' 634496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1239_2_checked : (List.range' 634624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1239_3_checked : (List.range' 634752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1239_range (index : Nat) (lower : 634368 ≤ index) (upper : index < 634880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 634624 then
    if cut : index < 634496 then
      exact segment_sound _ 634368 128 Restriction1239_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 634496 128 Restriction1239_1_checked index (by omega) (by omega)
  else
    if cut : index < 634752 then
      exact segment_sound _ 634624 128 Restriction1239_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 634752 128 Restriction1239_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
