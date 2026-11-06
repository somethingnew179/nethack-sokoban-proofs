import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1870_0_checked : (List.range' 957440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1870_1_checked : (List.range' 957568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1870_2_checked : (List.range' 957696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1870_3_checked : (List.range' 957824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1870_range (index : Nat) (lower : 957440 ≤ index) (upper : index < 957952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 957696 then
    if cut : index < 957568 then
      exact segment_sound _ 957440 128 Restriction1870_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 957568 128 Restriction1870_1_checked index (by omega) (by omega)
  else
    if cut : index < 957824 then
      exact segment_sound _ 957696 128 Restriction1870_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 957824 128 Restriction1870_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
