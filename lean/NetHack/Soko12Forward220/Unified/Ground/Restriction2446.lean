import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2446_0_checked : (List.range' 1252352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2446_1_checked : (List.range' 1252480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2446_2_checked : (List.range' 1252608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2446_3_checked : (List.range' 1252736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2446_range (index : Nat) (lower : 1252352 ≤ index) (upper : index < 1252864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1252608 then
    if cut : index < 1252480 then
      exact segment_sound _ 1252352 128 Restriction2446_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1252480 128 Restriction2446_1_checked index (by omega) (by omega)
  else
    if cut : index < 1252736 then
      exact segment_sound _ 1252608 128 Restriction2446_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1252736 128 Restriction2446_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
