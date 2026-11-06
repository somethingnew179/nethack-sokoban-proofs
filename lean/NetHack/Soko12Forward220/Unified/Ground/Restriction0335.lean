import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0335_0_checked : (List.range' 171520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0335_1_checked : (List.range' 171648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0335_2_checked : (List.range' 171776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0335_3_checked : (List.range' 171904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0335_range (index : Nat) (lower : 171520 ≤ index) (upper : index < 172032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 171776 then
    if cut : index < 171648 then
      exact segment_sound _ 171520 128 Restriction0335_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171648 128 Restriction0335_1_checked index (by omega) (by omega)
  else
    if cut : index < 171904 then
      exact segment_sound _ 171776 128 Restriction0335_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171904 128 Restriction0335_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
