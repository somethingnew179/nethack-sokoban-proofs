import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1308_0_checked : (List.range' 669696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1308_1_checked : (List.range' 669824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1308_2_checked : (List.range' 669952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1308_3_checked : (List.range' 670080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1308_range (index : Nat) (lower : 669696 ≤ index) (upper : index < 670208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 669952 then
    if cut : index < 669824 then
      exact segment_sound _ 669696 128 Restriction1308_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 669824 128 Restriction1308_1_checked index (by omega) (by omega)
  else
    if cut : index < 670080 then
      exact segment_sound _ 669952 128 Restriction1308_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 670080 128 Restriction1308_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
