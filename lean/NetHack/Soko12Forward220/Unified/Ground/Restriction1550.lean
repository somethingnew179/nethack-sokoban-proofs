import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1550_0_checked : (List.range' 793600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1550_1_checked : (List.range' 793728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1550_2_checked : (List.range' 793856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1550_3_checked : (List.range' 793984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1550_range (index : Nat) (lower : 793600 ≤ index) (upper : index < 794112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 793856 then
    if cut : index < 793728 then
      exact segment_sound _ 793600 128 Restriction1550_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 793728 128 Restriction1550_1_checked index (by omega) (by omega)
  else
    if cut : index < 793984 then
      exact segment_sound _ 793856 128 Restriction1550_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 793984 128 Restriction1550_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
