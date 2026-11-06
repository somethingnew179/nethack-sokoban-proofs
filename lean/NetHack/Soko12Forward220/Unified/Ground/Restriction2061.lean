import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2061_0_checked : (List.range' 1055232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2061_1_checked : (List.range' 1055360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2061_2_checked : (List.range' 1055488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2061_3_checked : (List.range' 1055616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2061_range (index : Nat) (lower : 1055232 ≤ index) (upper : index < 1055744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1055488 then
    if cut : index < 1055360 then
      exact segment_sound _ 1055232 128 Restriction2061_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1055360 128 Restriction2061_1_checked index (by omega) (by omega)
  else
    if cut : index < 1055616 then
      exact segment_sound _ 1055488 128 Restriction2061_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1055616 128 Restriction2061_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
