import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2182_0_checked : (List.range' 1117184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2182_1_checked : (List.range' 1117312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2182_2_checked : (List.range' 1117440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2182_3_checked : (List.range' 1117568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2182_range (index : Nat) (lower : 1117184 ≤ index) (upper : index < 1117696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1117440 then
    if cut : index < 1117312 then
      exact segment_sound _ 1117184 128 Restriction2182_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1117312 128 Restriction2182_1_checked index (by omega) (by omega)
  else
    if cut : index < 1117568 then
      exact segment_sound _ 1117440 128 Restriction2182_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1117568 128 Restriction2182_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
