import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2250_0_checked : (List.range' 1152000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2250_1_checked : (List.range' 1152128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2250_2_checked : (List.range' 1152256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2250_3_checked : (List.range' 1152384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2250_range (index : Nat) (lower : 1152000 ≤ index) (upper : index < 1152512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1152256 then
    if cut : index < 1152128 then
      exact segment_sound _ 1152000 128 Restriction2250_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1152128 128 Restriction2250_1_checked index (by omega) (by omega)
  else
    if cut : index < 1152384 then
      exact segment_sound _ 1152256 128 Restriction2250_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1152384 128 Restriction2250_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
