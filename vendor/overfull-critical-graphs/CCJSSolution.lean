/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import Overfull.Theorem12
public import Overfull.ChenCao

/-!
# Solution

`Overfull.IsClassTwo`, `Overfull.IsDeltaCritical` and `Overfull.IsOverfull` are defined in
`Overfull.Basic`; `Overfull.overfull_of_critical` is proved in `Overfull.Theorem12`, from the
kite lemmas (`Overfull.KiteG`, `Overfull.ShortKite`), the fork lemma (`Overfull.Fork`) and the
counting arguments of `Overfull.Theorem12a`–`Overfull.Theorem12d`.
`Overfull.overfull_of_critical_cc` and `Overfull.overfull_of_critical_ccjs` are proved in
`Overfull.ChenCao`, from the broom lemma (`Overfull.Broom`), the kite lemma without `c`
(`Overfull.Kite0D`) and the frame `Overfull.CCa`–`Overfull.CCd`.
-/
