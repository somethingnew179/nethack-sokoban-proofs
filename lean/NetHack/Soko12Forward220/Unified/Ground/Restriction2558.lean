import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2558_0_checked : (List.range' 1309696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2558_1_checked : (List.range' 1309824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2558_2_checked : (List.range' 1309952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2558_3_checked : (List.range' 1310080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2558_range (index : Nat) (lower : 1309696 ≤ index) (upper : index < 1310208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1309952 then
    if cut : index < 1309824 then
      exact segment_sound _ 1309696 128 Restriction2558_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1309824 128 Restriction2558_1_checked index (by omega) (by omega)
  else
    if cut : index < 1310080 then
      exact segment_sound _ 1309952 128 Restriction2558_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1310080 128 Restriction2558_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
