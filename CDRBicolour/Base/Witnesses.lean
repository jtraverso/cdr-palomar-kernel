/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Base.Data.W_1_2_4
public import CDRBicolour.Base.Data.W_1_4_4
public import CDRBicolour.Base.Data.W_2_5_6
public import CDRBicolour.Base.Data.W_4_6_9
public import CDRBicolour.Base.Data.W_4_8_9
public import CDRBicolour.Base.Data.W_5_6_10
public import CDRBicolour.Base.Data.W_5_10_10
public import CDRBicolour.Base.Data.W_6_9_12
public import CDRBicolour.Base.Data.W_8_9_14
public import CDRBicolour.Base.Data.W_9_12_16
public import CDRBicolour.Base.Data.W_9_14_16
public import CDRBicolour.Base.Data.W_10_12_17
public import CDRBicolour.Base.Data.W_10_16_17
public import CDRBicolour.Base.Data.W_12_17_20
public import CDRBicolour.Base.Data.W_14_14_21
public import CDRBicolour.Base.Data.W_16_20_25
public import CDRBicolour.Base.Data.W_17_24_26
public import CDRBicolour.Base.Data.W_21_22_30
public import CDRBicolour.Base.Data.W_22_25_32
public import CDRBicolour.Base.Data.W_26_34_37
public import CDRBicolour.Base.Data.W_30_32_41
public import CDRBicolour.Base.Data.W_30_37_42
public import CDRBicolour.Base.Data.W_33_44_44
public import CDRBicolour.Base.Data.W_36_42_49
public import CDRBicolour.Base.Data.W_41_44_54
public import CDRBicolour.Base.Data.W_44_49_58
public import CDRBicolour.Base.Data.W_44_56_57
public import CDRBicolour.Base.Data.W_46_57_60
public import CDRBicolour.Base.Data.W_54_58_69
public import CDRBicolour.Base.Data.W_56_65_72
public import CDRBicolour.Base.Data.W_57_70_72
public import CDRBicolour.Base.Data.W_65_66_80
public import CDRBicolour.Base.Data.W_65_76_82
public import CDRBicolour.Base.Data.W_69_74_86
public import CDRBicolour.Base.Data.W_70_85_86
public import CDRBicolour.Base.Data.W_81_90_100
public import CDRBicolour.Base.Data.W_82_94_101
public import CDRBicolour.Base.Data.W_86_92_105
public import CDRBicolour.Base.Data.W_85_102_102
public import CDRBicolour.Base.Data.W_96_97_114
public import CDRBicolour.Base.Data.W_97_100_116
public import CDRBicolour.Base.Data.W_104_121_124
public import CDRBicolour.Base.Data.W_112_121_134
public import CDRBicolour.Base.Data.W_114_129_136
public import CDRBicolour.Base.Data.W_133_134_154
public import CDRBicolour.Base.Data.W_132_145_156
public import CDRBicolour.Base.Data.W_137_142_160
public import CDRBicolour.Base.Data.W_142_149_166
public import CDRBicolour.Base.Data.W_154_156_177

/-! The 49 explicit witnesses of the finite base (profiles not covered by a uniform
branch nor by the descent L165). -/

@[expose] public section

namespace CDRBicolour.Base

/-- The profiles with explicit witnesses. -/
def witnessList : List (ℕ × ℕ × ℕ) := [
  (1, 2, 4),
  (1, 4, 4),
  (2, 5, 6),
  (4, 6, 9),
  (4, 8, 9),
  (5, 6, 10),
  (5, 10, 10),
  (6, 9, 12),
  (8, 9, 14),
  (9, 12, 16),
  (9, 14, 16),
  (10, 12, 17),
  (10, 16, 17),
  (12, 17, 20),
  (14, 14, 21),
  (16, 20, 25),
  (17, 24, 26),
  (21, 22, 30),
  (22, 25, 32),
  (26, 34, 37),
  (30, 32, 41),
  (30, 37, 42),
  (33, 44, 44),
  (36, 42, 49),
  (41, 44, 54),
  (44, 49, 58),
  (44, 56, 57),
  (46, 57, 60),
  (54, 58, 69),
  (56, 65, 72),
  (57, 70, 72),
  (65, 66, 80),
  (65, 76, 82),
  (69, 74, 86),
  (70, 85, 86),
  (81, 90, 100),
  (82, 94, 101),
  (86, 92, 105),
  (85, 102, 102),
  (96, 97, 114),
  (97, 100, 116),
  (104, 121, 124),
  (112, 121, 134),
  (114, 129, 136),
  (133, 134, 154),
  (132, 145, 156),
  (137, 142, 160),
  (142, 149, 166),
  (154, 156, 177)]

theorem witness_realises : ∀ t ∈ witnessList, Realises t.1 t.2.1 t.2.2 := by
  intro t ht
  simp only [witnessList, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Data.realises_1_2_4
  · exact Data.realises_1_4_4
  · exact Data.realises_2_5_6
  · exact Data.realises_4_6_9
  · exact Data.realises_4_8_9
  · exact Data.realises_5_6_10
  · exact Data.realises_5_10_10
  · exact Data.realises_6_9_12
  · exact Data.realises_8_9_14
  · exact Data.realises_9_12_16
  · exact Data.realises_9_14_16
  · exact Data.realises_10_12_17
  · exact Data.realises_10_16_17
  · exact Data.realises_12_17_20
  · exact Data.realises_14_14_21
  · exact Data.realises_16_20_25
  · exact Data.realises_17_24_26
  · exact Data.realises_21_22_30
  · exact Data.realises_22_25_32
  · exact Data.realises_26_34_37
  · exact Data.realises_30_32_41
  · exact Data.realises_30_37_42
  · exact Data.realises_33_44_44
  · exact Data.realises_36_42_49
  · exact Data.realises_41_44_54
  · exact Data.realises_44_49_58
  · exact Data.realises_44_56_57
  · exact Data.realises_46_57_60
  · exact Data.realises_54_58_69
  · exact Data.realises_56_65_72
  · exact Data.realises_57_70_72
  · exact Data.realises_65_66_80
  · exact Data.realises_65_76_82
  · exact Data.realises_69_74_86
  · exact Data.realises_70_85_86
  · exact Data.realises_81_90_100
  · exact Data.realises_82_94_101
  · exact Data.realises_86_92_105
  · exact Data.realises_85_102_102
  · exact Data.realises_96_97_114
  · exact Data.realises_97_100_116
  · exact Data.realises_104_121_124
  · exact Data.realises_112_121_134
  · exact Data.realises_114_129_136
  · exact Data.realises_133_134_154
  · exact Data.realises_132_145_156
  · exact Data.realises_137_142_160
  · exact Data.realises_142_149_166
  · exact Data.realises_154_156_177

end CDRBicolour.Base
