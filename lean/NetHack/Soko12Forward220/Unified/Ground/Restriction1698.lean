import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1698_0_checked : (List.range' 869376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1698_1_checked : (List.range' 869504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1698_2_checked : (List.range' 869632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1698_3_checked : (List.range' 869760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1698_range (index : Nat) (lower : 869376 ≤ index) (upper : index < 869888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 869632 then
    if cut : index < 869504 then
      exact segment_sound _ 869376 128 Restriction1698_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 869504 128 Restriction1698_1_checked index (by omega) (by omega)
  else
    if cut : index < 869760 then
      exact segment_sound _ 869632 128 Restriction1698_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 869760 128 Restriction1698_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
