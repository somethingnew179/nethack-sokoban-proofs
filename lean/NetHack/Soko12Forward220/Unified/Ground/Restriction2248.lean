import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2248_0_checked : (List.range' 1150976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2248_1_checked : (List.range' 1151104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2248_2_checked : (List.range' 1151232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2248_3_checked : (List.range' 1151360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2248_range (index : Nat) (lower : 1150976 ≤ index) (upper : index < 1151488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1151232 then
    if cut : index < 1151104 then
      exact segment_sound _ 1150976 128 Restriction2248_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1151104 128 Restriction2248_1_checked index (by omega) (by omega)
  else
    if cut : index < 1151360 then
      exact segment_sound _ 1151232 128 Restriction2248_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1151360 128 Restriction2248_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
