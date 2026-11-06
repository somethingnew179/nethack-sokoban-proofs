import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1834_0_checked : (List.range' 939008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1834_1_checked : (List.range' 939136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1834_2_checked : (List.range' 939264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1834_3_checked : (List.range' 939392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1834_range (index : Nat) (lower : 939008 ≤ index) (upper : index < 939520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 939264 then
    if cut : index < 939136 then
      exact segment_sound _ 939008 128 Restriction1834_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 939136 128 Restriction1834_1_checked index (by omega) (by omega)
  else
    if cut : index < 939392 then
      exact segment_sound _ 939264 128 Restriction1834_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 939392 128 Restriction1834_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
