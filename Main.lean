import Test.Lean
import Lean
open Lean Elab PrettyPrinter

unsafe def parse (env : Environment) (input : String) (fileName : String) : IO Unit := do
  let stx ← match Parser.runParserCategory env `com_syn input fileName with
    | Except.ok stx => pure stx
    | Except.error errmsg => throw (IO.userError errmsg)
  let c ← IMP.elabCom stx
  IMP.printCom c
  IO.println ""

def failWith (msg : String) (exitCode : UInt8 := 1) : IO α := do
  (← IO.getStderr).putStrLn msg
  IO.Process.exit exitCode

unsafe def main (args : List String) : IO Unit := do
  let [fileName] := args | failWith "Usage: reformat file"
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile fileName
  let env ← Lean.importModules #[`Test.Lean] {}
  parse env input fileName
