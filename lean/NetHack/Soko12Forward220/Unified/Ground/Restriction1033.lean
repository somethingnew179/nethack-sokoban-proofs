import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1033_0_checked : (List.range' 528896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1033_1_checked : (List.range' 529024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1033_2_checked : (List.range' 529152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1033_3_checked : (List.range' 529280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1033_range (index : Nat) (lower : 528896 ≤ index) (upper : index < 529408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 529152 then
    if cut : index < 529024 then
      exact segment_sound _ 528896 128 Restriction1033_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 529024 128 Restriction1033_1_checked index (by omega) (by omega)
  else
    if cut : index < 529280 then
      exact segment_sound _ 529152 128 Restriction1033_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 529280 128 Restriction1033_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
