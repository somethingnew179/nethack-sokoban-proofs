import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1554_0_checked : (List.range' 795648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1554_1_checked : (List.range' 795776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1554_2_checked : (List.range' 795904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1554_3_checked : (List.range' 796032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1554_range (index : Nat) (lower : 795648 ≤ index) (upper : index < 796160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 795904 then
    if cut : index < 795776 then
      exact segment_sound _ 795648 128 Restriction1554_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 795776 128 Restriction1554_1_checked index (by omega) (by omega)
  else
    if cut : index < 796032 then
      exact segment_sound _ 795904 128 Restriction1554_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 796032 128 Restriction1554_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
