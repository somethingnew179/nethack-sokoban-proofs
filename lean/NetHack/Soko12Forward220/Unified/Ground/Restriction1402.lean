import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1402_0_checked : (List.range' 717824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1402_1_checked : (List.range' 717952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1402_2_checked : (List.range' 718080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1402_3_checked : (List.range' 718208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1402_range (index : Nat) (lower : 717824 ≤ index) (upper : index < 718336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 718080 then
    if cut : index < 717952 then
      exact segment_sound _ 717824 128 Restriction1402_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 717952 128 Restriction1402_1_checked index (by omega) (by omega)
  else
    if cut : index < 718208 then
      exact segment_sound _ 718080 128 Restriction1402_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 718208 128 Restriction1402_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
