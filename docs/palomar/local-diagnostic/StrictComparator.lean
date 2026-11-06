module
import Lake.Check.Compare
import Lake.Check.Axioms
import LeanExport.Parse

public def main : IO Unit := do
  let dir := System.FilePath.mk "C:/nw/cdr-palomar-private-state"
  let challenge ← LeanExport.parseStream <| .ofHandle
    (← IO.FS.Handle.mk (dir / "diagnostic-challenge.ndjson") .read)
  let solution ← LeanExport.parseStream <| .ofHandle
    (← IO.FS.Handle.mk (dir / "diagnostic-solution.ndjson") .read)
  let targets := #[`CDRBicolour.cdr_conjecture, `CDRBicolour.cdr_characterization,
    `CDRBicolour.Absorption.Corners.cdr_type_spectrum]
  let axioms := #[`propext, `Classical.choice, `Quot.sound]
  let primitives := #[`Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd,
    `Nat.div, `Nat.mod, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor,
    `Nat.shiftLeft, `Nat.shiftRight, `String.ofList, `Char.ofNat, `List,
    `eagerReduce, `Nat, `String, `String.mk, `Char, `optParam, `autoParam,
    `semiOutParam, `outParam, `Quot, `Quot.mk, `Quot.lift, `Quot.ind]
  IO.println "Parsed both completed exports; comparing statements and primitive constants"
  IO.ofExcept <| Lake.Check.compareAt challenge solution (targets ++ axioms) #[] primitives
  IO.ofExcept <| Lake.Check.checkAxioms solution targets #[] axioms
  IO.println "PASS: strict Lake structural comparison and standard-axiom whitelist"
  IO.println "Local diagnostic only; not the official sandboxed Palomar preflight"
