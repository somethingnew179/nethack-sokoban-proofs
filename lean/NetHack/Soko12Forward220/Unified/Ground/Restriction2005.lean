import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2005_0_checked : (List.range' 1026560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2005_1_checked : (List.range' 1026688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2005_2_checked : (List.range' 1026816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2005_3_checked : (List.range' 1026944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2005_range (index : Nat) (lower : 1026560 ≤ index) (upper : index < 1027072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1026816 then
    if cut : index < 1026688 then
      exact segment_sound _ 1026560 128 Restriction2005_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1026688 128 Restriction2005_1_checked index (by omega) (by omega)
  else
    if cut : index < 1026944 then
      exact segment_sound _ 1026816 128 Restriction2005_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1026944 128 Restriction2005_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
