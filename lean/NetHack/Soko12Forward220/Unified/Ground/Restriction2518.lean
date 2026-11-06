import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2518_0_checked : (List.range' 1289216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2518_1_checked : (List.range' 1289344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2518_2_checked : (List.range' 1289472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2518_3_checked : (List.range' 1289600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2518_range (index : Nat) (lower : 1289216 ≤ index) (upper : index < 1289728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1289472 then
    if cut : index < 1289344 then
      exact segment_sound _ 1289216 128 Restriction2518_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1289344 128 Restriction2518_1_checked index (by omega) (by omega)
  else
    if cut : index < 1289600 then
      exact segment_sound _ 1289472 128 Restriction2518_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1289600 128 Restriction2518_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
