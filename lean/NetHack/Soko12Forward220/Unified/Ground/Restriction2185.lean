import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2185_0_checked : (List.range' 1118720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2185_1_checked : (List.range' 1118848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2185_2_checked : (List.range' 1118976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2185_3_checked : (List.range' 1119104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2185_range (index : Nat) (lower : 1118720 ≤ index) (upper : index < 1119232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1118976 then
    if cut : index < 1118848 then
      exact segment_sound _ 1118720 128 Restriction2185_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1118848 128 Restriction2185_1_checked index (by omega) (by omega)
  else
    if cut : index < 1119104 then
      exact segment_sound _ 1118976 128 Restriction2185_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1119104 128 Restriction2185_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
