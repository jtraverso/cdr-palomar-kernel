module
public import Lean
public meta import Lean

public meta section
namespace CDRSurfaceAudit
open Lean Meta

def names : Array Name := #[
  `CDRBicolour.STS, `CDRBicolour.STS.mk, `CDRBicolour.STS.blocks,
  `CDRBicolour.STS.card_eq_three, `CDRBicolour.STS.existsUnique_block,
  `CDRBicolour.IsStrictBicolouring, `CDRBicolour.classSize,
  `CDRBicolour.AdmissibleProfile, `CDRBicolour.Realises, `CDRBicolour.CDRConjecture,
  `CDRBicolour.Prefix.col3, `CDRBicolour.BlockTypes.cnt,
  `CDRBicolour.BlockTypes.typeCount, `CDRBicolour.Absorption.Corners.sz,
  `CDRBicolour.Absorption.Corners.LowerNec, `CDRBicolour.Absorption.Corners.ExactNec,
  `CDRBicolour.Absorption.Corners.AACSpec,
  `CDRBicolour.cdr_conjecture, `CDRBicolour.cdr_characterization,
  `CDRBicolour.Absorption.Corners.cdr_type_spectrum]

/-- Discard binder labels and annotations; preserve all bound-variable indices. -/
partial def canonical (e : Expr) : MetaM Expr := do
  match e with
  | .app f x => return .app (← canonical f) (← canonical x)
  | .lam _ t b _ => return .lam .anonymous (← canonical t) (← canonical b) .default
  | .forallE _ t b _ => return .forallE .anonymous (← canonical t) (← canonical b) .default
  | .letE _ t v b n => return .letE .anonymous (← canonical t) (← canonical v) (← canonical b) n
  | .mdata _ e => canonical e
  | .proj n i e => return .proj n i (← canonical e)
  | .const name levels =>
    -- Exported proof interfaces may be axiomInfo even when their private
    -- implementations are proved. Classify by the checked type, not the tag.
    if ← isProof e then
      let proposition ← reduce (← inferType e)
      return .app (.const `CDRSurfaceAudit.erasedProof []) (← canonical proposition)
    else
      match (← getEnv).find? name with
      | some (.defnInfo info) =>
        if name.getString!.startsWith "_proof_" then
          canonical (info.value.instantiateLevelParams info.levelParams levels)
        else return e
      | _ => return e
  | _ => return e

def dump (path : System.FilePath) : MetaM Unit := do
  let env ← getEnv
  let mut rows := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing declaration: {name}"
    let kind := match info with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | _ => "other"
    let mut body := Json.null
    if let .defnInfo v := info then
      let value ← canonical v.value
      body := toJson (reprStr value)
    let typeExpr ← canonical info.type
    rows := rows.push <| Json.mkObj [("name", toJson name.toString),
      ("kind", toJson kind), ("type", toJson (reprStr typeExpr)),
      ("body", body)]
  IO.FS.writeFile path (Json.arr rows).pretty
end CDRSurfaceAudit
