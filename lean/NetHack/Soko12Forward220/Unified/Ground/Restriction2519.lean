import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2519_0_checked : (List.range' 1289728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2519_1_checked : (List.range' 1289856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2519_2_checked : (List.range' 1289984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2519_3_checked : (List.range' 1290112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2519_range (index : Nat) (lower : 1289728 ≤ index) (upper : index < 1290240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1289984 then
    if cut : index < 1289856 then
      exact segment_sound _ 1289728 128 Restriction2519_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1289856 128 Restriction2519_1_checked index (by omega) (by omega)
  else
    if cut : index < 1290112 then
      exact segment_sound _ 1289984 128 Restriction2519_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1290112 128 Restriction2519_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
