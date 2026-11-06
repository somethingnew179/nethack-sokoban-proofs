import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2389_0_checked : (List.range' 1223168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2389_1_checked : (List.range' 1223296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2389_2_checked : (List.range' 1223424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2389_3_checked : (List.range' 1223552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2389_range (index : Nat) (lower : 1223168 ≤ index) (upper : index < 1223680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1223424 then
    if cut : index < 1223296 then
      exact segment_sound _ 1223168 128 Restriction2389_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1223296 128 Restriction2389_1_checked index (by omega) (by omega)
  else
    if cut : index < 1223552 then
      exact segment_sound _ 1223424 128 Restriction2389_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1223552 128 Restriction2389_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
