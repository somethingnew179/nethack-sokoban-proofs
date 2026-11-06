import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1974_0_checked : (List.range' 1010688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1974_1_checked : (List.range' 1010816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1974_2_checked : (List.range' 1010944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1974_3_checked : (List.range' 1011072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1974_range (index : Nat) (lower : 1010688 ≤ index) (upper : index < 1011200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1010944 then
    if cut : index < 1010816 then
      exact segment_sound _ 1010688 128 Restriction1974_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1010816 128 Restriction1974_1_checked index (by omega) (by omega)
  else
    if cut : index < 1011072 then
      exact segment_sound _ 1010944 128 Restriction1974_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1011072 128 Restriction1974_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
