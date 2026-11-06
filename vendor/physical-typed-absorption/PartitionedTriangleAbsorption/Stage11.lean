/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage10
public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.RefinerObstruction
public import PartitionedTriangleAbsorption.ModThreeLayer
public import PartitionedTriangleAbsorption.ParityChain
public import PartitionedTriangleAbsorption.RefinerConstructionBudget
public import PartitionedTriangleAbsorption.RootedEmbeddingSelection
public import PartitionedTriangleAbsorption.RootedTemplateEmbedding
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Accepted local refiner and rooted-embedding interfaces

This checkpoint does not assert existence of the complete ordinary refiner,
private absorber templates, a typed omniabsorber or the final Theorem 13.16.
-/
