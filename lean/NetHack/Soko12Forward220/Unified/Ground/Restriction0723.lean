import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0723_0_checked : (List.range' 370176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0723_1_checked : (List.range' 370304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0723_2_checked : (List.range' 370432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0723_3_checked : (List.range' 370560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0723_range (index : Nat) (lower : 370176 ≤ index) (upper : index < 370688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 370432 then
    if cut : index < 370304 then
      exact segment_sound _ 370176 128 Restriction0723_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 370304 128 Restriction0723_1_checked index (by omega) (by omega)
  else
    if cut : index < 370560 then
      exact segment_sound _ 370432 128 Restriction0723_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 370560 128 Restriction0723_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
