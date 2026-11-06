import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Numeric0070_0_checked : (List.range' 35840 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0070_1_checked : (List.range' 35968 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0070_2_checked : (List.range' 36096 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0070_3_checked : (List.range' 36224 128).all (fun index => DecisionDAGCountedBounded.checkRow read bounds numeric index) = true := by decide +kernel
theorem Numeric0070_range (index : Nat) (lower : 35840 ≤ index) (upper : index < 36352) : DecisionDAGCountedBounded.checkRow read bounds numeric index = true := by
  if cut : index < 36096 then
    if cut : index < 35968 then
      exact segment_sound _ 35840 128 Numeric0070_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 35968 128 Numeric0070_1_checked index (by omega) (by omega)
  else
    if cut : index < 36224 then
      exact segment_sound _ 36096 128 Numeric0070_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 36224 128 Numeric0070_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
