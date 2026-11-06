import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0920_0_checked : (List.range' 471040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0920_1_checked : (List.range' 471168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0920_2_checked : (List.range' 471296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0920_3_checked : (List.range' 471424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0920_range (index : Nat) (lower : 471040 ≤ index) (upper : index < 471552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 471296 then
    if cut : index < 471168 then
      exact segment_sound _ 471040 128 Restriction0920_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 471168 128 Restriction0920_1_checked index (by omega) (by omega)
  else
    if cut : index < 471424 then
      exact segment_sound _ 471296 128 Restriction0920_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 471424 128 Restriction0920_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
