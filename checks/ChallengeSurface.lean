module
import CDRPreprintsChallenge
import checks.StatementSurface
public meta import checks.StatementSurface

run_cmd Lean.Elab.Command.liftTermElabM do
  CDRSurfaceAudit.dump "docs/palomar/CHALLENGE_SURFACE.json"
