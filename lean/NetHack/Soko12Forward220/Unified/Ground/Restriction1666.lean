import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1666_0_checked : (List.range' 852992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1666_1_checked : (List.range' 853120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1666_2_checked : (List.range' 853248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1666_3_checked : (List.range' 853376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1666_range (index : Nat) (lower : 852992 ≤ index) (upper : index < 853504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 853248 then
    if cut : index < 853120 then
      exact segment_sound _ 852992 128 Restriction1666_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 853120 128 Restriction1666_1_checked index (by omega) (by omega)
  else
    if cut : index < 853376 then
      exact segment_sound _ 853248 128 Restriction1666_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 853376 128 Restriction1666_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
