import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1143_0_checked : (List.range' 585216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1143_1_checked : (List.range' 585344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1143_2_checked : (List.range' 585472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1143_3_checked : (List.range' 585600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1143_range (index : Nat) (lower : 585216 ≤ index) (upper : index < 585728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 585472 then
    if cut : index < 585344 then
      exact segment_sound _ 585216 128 Restriction1143_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 585344 128 Restriction1143_1_checked index (by omega) (by omega)
  else
    if cut : index < 585600 then
      exact segment_sound _ 585472 128 Restriction1143_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 585600 128 Restriction1143_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
