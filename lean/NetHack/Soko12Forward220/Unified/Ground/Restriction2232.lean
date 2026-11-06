import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2232_0_checked : (List.range' 1142784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2232_1_checked : (List.range' 1142912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2232_2_checked : (List.range' 1143040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2232_3_checked : (List.range' 1143168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2232_range (index : Nat) (lower : 1142784 ≤ index) (upper : index < 1143296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1143040 then
    if cut : index < 1142912 then
      exact segment_sound _ 1142784 128 Restriction2232_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1142912 128 Restriction2232_1_checked index (by omega) (by omega)
  else
    if cut : index < 1143168 then
      exact segment_sound _ 1143040 128 Restriction2232_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1143168 128 Restriction2232_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
