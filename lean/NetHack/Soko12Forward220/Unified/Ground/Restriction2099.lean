import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2099_0_checked : (List.range' 1074688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2099_1_checked : (List.range' 1074816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2099_2_checked : (List.range' 1074944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2099_3_checked : (List.range' 1075072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2099_range (index : Nat) (lower : 1074688 ≤ index) (upper : index < 1075200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1074944 then
    if cut : index < 1074816 then
      exact segment_sound _ 1074688 128 Restriction2099_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1074816 128 Restriction2099_1_checked index (by omega) (by omega)
  else
    if cut : index < 1075072 then
      exact segment_sound _ 1074944 128 Restriction2099_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1075072 128 Restriction2099_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
