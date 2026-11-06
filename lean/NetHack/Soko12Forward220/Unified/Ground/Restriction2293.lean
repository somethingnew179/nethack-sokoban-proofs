import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2293_0_checked : (List.range' 1174016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2293_1_checked : (List.range' 1174144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2293_2_checked : (List.range' 1174272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2293_3_checked : (List.range' 1174400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2293_range (index : Nat) (lower : 1174016 ≤ index) (upper : index < 1174528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1174272 then
    if cut : index < 1174144 then
      exact segment_sound _ 1174016 128 Restriction2293_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1174144 128 Restriction2293_1_checked index (by omega) (by omega)
  else
    if cut : index < 1174400 then
      exact segment_sound _ 1174272 128 Restriction2293_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1174400 128 Restriction2293_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
