import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1615_0_checked : (List.range' 826880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1615_1_checked : (List.range' 827008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1615_2_checked : (List.range' 827136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1615_3_checked : (List.range' 827264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1615_range (index : Nat) (lower : 826880 ≤ index) (upper : index < 827392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 827136 then
    if cut : index < 827008 then
      exact segment_sound _ 826880 128 Restriction1615_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 827008 128 Restriction1615_1_checked index (by omega) (by omega)
  else
    if cut : index < 827264 then
      exact segment_sound _ 827136 128 Restriction1615_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 827264 128 Restriction1615_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
