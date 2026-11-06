import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1710_0_checked : (List.range' 875520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1710_1_checked : (List.range' 875648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1710_2_checked : (List.range' 875776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1710_3_checked : (List.range' 875904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1710_range (index : Nat) (lower : 875520 ≤ index) (upper : index < 876032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 875776 then
    if cut : index < 875648 then
      exact segment_sound _ 875520 128 Restriction1710_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 875648 128 Restriction1710_1_checked index (by omega) (by omega)
  else
    if cut : index < 875904 then
      exact segment_sound _ 875776 128 Restriction1710_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 875904 128 Restriction1710_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
