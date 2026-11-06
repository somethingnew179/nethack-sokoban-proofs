import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0452_0_checked : (List.range' 231424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0452_1_checked : (List.range' 231552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0452_2_checked : (List.range' 231680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0452_3_checked : (List.range' 231808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0452_range (index : Nat) (lower : 231424 ≤ index) (upper : index < 231936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 231680 then
    if cut : index < 231552 then
      exact segment_sound _ 231424 128 Restriction0452_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231552 128 Restriction0452_1_checked index (by omega) (by omega)
  else
    if cut : index < 231808 then
      exact segment_sound _ 231680 128 Restriction0452_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231808 128 Restriction0452_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
