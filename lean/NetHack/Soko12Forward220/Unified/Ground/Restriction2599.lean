import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2599_0_checked : (List.range' 1330688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2599_1_checked : (List.range' 1330816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2599_2_checked : (List.range' 1330944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2599_3_checked : (List.range' 1331072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2599_range (index : Nat) (lower : 1330688 ≤ index) (upper : index < 1331200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1330944 then
    if cut : index < 1330816 then
      exact segment_sound _ 1330688 128 Restriction2599_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1330816 128 Restriction2599_1_checked index (by omega) (by omega)
  else
    if cut : index < 1331072 then
      exact segment_sound _ 1330944 128 Restriction2599_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1331072 128 Restriction2599_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
