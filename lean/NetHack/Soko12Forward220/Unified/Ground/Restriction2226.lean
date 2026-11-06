import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2226_0_checked : (List.range' 1139712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2226_1_checked : (List.range' 1139840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2226_2_checked : (List.range' 1139968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2226_3_checked : (List.range' 1140096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2226_range (index : Nat) (lower : 1139712 ≤ index) (upper : index < 1140224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1139968 then
    if cut : index < 1139840 then
      exact segment_sound _ 1139712 128 Restriction2226_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1139840 128 Restriction2226_1_checked index (by omega) (by omega)
  else
    if cut : index < 1140096 then
      exact segment_sound _ 1139968 128 Restriction2226_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1140096 128 Restriction2226_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
