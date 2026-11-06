import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2022_0_checked : (List.range' 1035264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2022_1_checked : (List.range' 1035392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2022_2_checked : (List.range' 1035520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2022_3_checked : (List.range' 1035648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2022_range (index : Nat) (lower : 1035264 ≤ index) (upper : index < 1035776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1035520 then
    if cut : index < 1035392 then
      exact segment_sound _ 1035264 128 Restriction2022_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1035392 128 Restriction2022_1_checked index (by omega) (by omega)
  else
    if cut : index < 1035648 then
      exact segment_sound _ 1035520 128 Restriction2022_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1035648 128 Restriction2022_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
