import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2310_0_checked : (List.range' 1182720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2310_1_checked : (List.range' 1182848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2310_2_checked : (List.range' 1182976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2310_3_checked : (List.range' 1183104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2310_range (index : Nat) (lower : 1182720 ≤ index) (upper : index < 1183232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1182976 then
    if cut : index < 1182848 then
      exact segment_sound _ 1182720 128 Restriction2310_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1182848 128 Restriction2310_1_checked index (by omega) (by omega)
  else
    if cut : index < 1183104 then
      exact segment_sound _ 1182976 128 Restriction2310_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1183104 128 Restriction2310_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
