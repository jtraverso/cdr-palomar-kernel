module
import CDRBicolour.Characterization
import CDRBicolour.Absorption.Corners.Spectrum
import checks.StatementSurface
public meta import checks.StatementSurface

run_cmd Lean.Elab.Command.liftTermElabM do
  CDRSurfaceAudit.dump "docs/palomar/SOLUTION_SURFACE.json"
