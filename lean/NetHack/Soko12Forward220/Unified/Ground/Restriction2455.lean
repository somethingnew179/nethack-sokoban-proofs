import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2455_0_checked : (List.range' 1256960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2455_1_checked : (List.range' 1257088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2455_2_checked : (List.range' 1257216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2455_3_checked : (List.range' 1257344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2455_range (index : Nat) (lower : 1256960 ≤ index) (upper : index < 1257472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1257216 then
    if cut : index < 1257088 then
      exact segment_sound _ 1256960 128 Restriction2455_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1257088 128 Restriction2455_1_checked index (by omega) (by omega)
  else
    if cut : index < 1257344 then
      exact segment_sound _ 1257216 128 Restriction2455_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1257344 128 Restriction2455_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
