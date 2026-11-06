import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2365_0_checked : (List.range' 1210880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2365_1_checked : (List.range' 1211008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2365_2_checked : (List.range' 1211136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2365_3_checked : (List.range' 1211264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2365_range (index : Nat) (lower : 1210880 ≤ index) (upper : index < 1211392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1211136 then
    if cut : index < 1211008 then
      exact segment_sound _ 1210880 128 Restriction2365_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1211008 128 Restriction2365_1_checked index (by omega) (by omega)
  else
    if cut : index < 1211264 then
      exact segment_sound _ 1211136 128 Restriction2365_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1211264 128 Restriction2365_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
