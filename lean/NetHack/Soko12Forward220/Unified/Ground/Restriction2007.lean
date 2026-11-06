import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2007_0_checked : (List.range' 1027584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2007_1_checked : (List.range' 1027712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2007_2_checked : (List.range' 1027840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2007_3_checked : (List.range' 1027968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2007_range (index : Nat) (lower : 1027584 ≤ index) (upper : index < 1028096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1027840 then
    if cut : index < 1027712 then
      exact segment_sound _ 1027584 128 Restriction2007_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1027712 128 Restriction2007_1_checked index (by omega) (by omega)
  else
    if cut : index < 1027968 then
      exact segment_sound _ 1027840 128 Restriction2007_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1027968 128 Restriction2007_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
