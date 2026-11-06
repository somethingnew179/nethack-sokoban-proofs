import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1843_0_checked : (List.range' 943616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1843_1_checked : (List.range' 943744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1843_2_checked : (List.range' 943872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1843_3_checked : (List.range' 944000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1843_range (index : Nat) (lower : 943616 ≤ index) (upper : index < 944128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 943872 then
    if cut : index < 943744 then
      exact segment_sound _ 943616 128 Restriction1843_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 943744 128 Restriction1843_1_checked index (by omega) (by omega)
  else
    if cut : index < 944000 then
      exact segment_sound _ 943872 128 Restriction1843_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 944000 128 Restriction1843_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
