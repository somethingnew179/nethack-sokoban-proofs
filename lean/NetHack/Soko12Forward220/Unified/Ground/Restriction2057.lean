import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2057_0_checked : (List.range' 1053184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2057_1_checked : (List.range' 1053312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2057_2_checked : (List.range' 1053440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2057_3_checked : (List.range' 1053568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2057_range (index : Nat) (lower : 1053184 ≤ index) (upper : index < 1053696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1053440 then
    if cut : index < 1053312 then
      exact segment_sound _ 1053184 128 Restriction2057_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1053312 128 Restriction2057_1_checked index (by omega) (by omega)
  else
    if cut : index < 1053568 then
      exact segment_sound _ 1053440 128 Restriction2057_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1053568 128 Restriction2057_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
