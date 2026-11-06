import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2449_0_checked : (List.range' 1253888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2449_1_checked : (List.range' 1254016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2449_2_checked : (List.range' 1254144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2449_3_checked : (List.range' 1254272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2449_range (index : Nat) (lower : 1253888 ≤ index) (upper : index < 1254400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1254144 then
    if cut : index < 1254016 then
      exact segment_sound _ 1253888 128 Restriction2449_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1254016 128 Restriction2449_1_checked index (by omega) (by omega)
  else
    if cut : index < 1254272 then
      exact segment_sound _ 1254144 128 Restriction2449_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1254272 128 Restriction2449_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
