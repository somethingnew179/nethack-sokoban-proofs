import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1764_0_checked : (List.range' 903168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1764_1_checked : (List.range' 903296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1764_2_checked : (List.range' 903424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1764_3_checked : (List.range' 903552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1764_range (index : Nat) (lower : 903168 ≤ index) (upper : index < 903680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 903424 then
    if cut : index < 903296 then
      exact segment_sound _ 903168 128 Restriction1764_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 903296 128 Restriction1764_1_checked index (by omega) (by omega)
  else
    if cut : index < 903552 then
      exact segment_sound _ 903424 128 Restriction1764_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 903552 128 Restriction1764_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
