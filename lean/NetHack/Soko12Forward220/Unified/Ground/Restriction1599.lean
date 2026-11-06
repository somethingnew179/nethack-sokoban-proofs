import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1599_0_checked : (List.range' 818688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1599_1_checked : (List.range' 818816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1599_2_checked : (List.range' 818944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1599_3_checked : (List.range' 819072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1599_range (index : Nat) (lower : 818688 ≤ index) (upper : index < 819200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 818944 then
    if cut : index < 818816 then
      exact segment_sound _ 818688 128 Restriction1599_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 818816 128 Restriction1599_1_checked index (by omega) (by omega)
  else
    if cut : index < 819072 then
      exact segment_sound _ 818944 128 Restriction1599_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 819072 128 Restriction1599_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
