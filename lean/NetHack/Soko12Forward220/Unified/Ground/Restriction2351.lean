import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2351_0_checked : (List.range' 1203712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2351_1_checked : (List.range' 1203840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2351_2_checked : (List.range' 1203968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2351_3_checked : (List.range' 1204096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2351_range (index : Nat) (lower : 1203712 ≤ index) (upper : index < 1204224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1203968 then
    if cut : index < 1203840 then
      exact segment_sound _ 1203712 128 Restriction2351_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1203840 128 Restriction2351_1_checked index (by omega) (by omega)
  else
    if cut : index < 1204096 then
      exact segment_sound _ 1203968 128 Restriction2351_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1204096 128 Restriction2351_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
