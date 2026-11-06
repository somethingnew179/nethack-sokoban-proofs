import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2482_0_checked : (List.range' 1270784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2482_1_checked : (List.range' 1270912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2482_2_checked : (List.range' 1271040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2482_3_checked : (List.range' 1271168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2482_range (index : Nat) (lower : 1270784 ≤ index) (upper : index < 1271296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1271040 then
    if cut : index < 1270912 then
      exact segment_sound _ 1270784 128 Restriction2482_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1270912 128 Restriction2482_1_checked index (by omega) (by omega)
  else
    if cut : index < 1271168 then
      exact segment_sound _ 1271040 128 Restriction2482_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1271168 128 Restriction2482_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
