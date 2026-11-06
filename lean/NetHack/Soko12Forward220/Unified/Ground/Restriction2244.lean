import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2244_0_checked : (List.range' 1148928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2244_1_checked : (List.range' 1149056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2244_2_checked : (List.range' 1149184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2244_3_checked : (List.range' 1149312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2244_range (index : Nat) (lower : 1148928 ≤ index) (upper : index < 1149440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1149184 then
    if cut : index < 1149056 then
      exact segment_sound _ 1148928 128 Restriction2244_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1149056 128 Restriction2244_1_checked index (by omega) (by omega)
  else
    if cut : index < 1149312 then
      exact segment_sound _ 1149184 128 Restriction2244_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1149312 128 Restriction2244_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
