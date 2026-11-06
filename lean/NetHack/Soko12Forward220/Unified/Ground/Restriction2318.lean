import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2318_0_checked : (List.range' 1186816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2318_1_checked : (List.range' 1186944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2318_2_checked : (List.range' 1187072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2318_3_checked : (List.range' 1187200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2318_range (index : Nat) (lower : 1186816 ≤ index) (upper : index < 1187328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1187072 then
    if cut : index < 1186944 then
      exact segment_sound _ 1186816 128 Restriction2318_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1186944 128 Restriction2318_1_checked index (by omega) (by omega)
  else
    if cut : index < 1187200 then
      exact segment_sound _ 1187072 128 Restriction2318_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1187200 128 Restriction2318_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
