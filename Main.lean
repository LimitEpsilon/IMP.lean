import «Test».«Lean»
import Lean
open Lean Elab PrettyPrinter

unsafe def parse (input : String) (fileName : String) : MetaM IMP.com := do
  let stx ← Lean.ofExcept <| Parser.runParserCategory (← getEnv) `com_syn input fileName
  let exp ← IMP.elabCom stx
  let c : IMP.com ← Meta.evalExpr IMP.com (Expr.const ``IMP.com []) exp
  return c

unsafe def x := do
  let c ← parse "if 3 < 4 then
      c := 5
      else
        a := a + 1
      fi;;
      b := 10" "aaa"
  IMP.printCom c

#eval x

unsafe def main (args : List String) : IO Unit := do
  return ()
  -- let [fileName] := args | failWith "Usage: reformat file"
  -- initSearchPath (← findSysroot)
  -- let input ← IO.FS.readFile fileName
  -- let moduleStx ← parseModule input fileName
  -- let leadingUpdated := mkNullNode (moduleStx.map (·.stx)) |>.updateLeading |>.getArgs
  -- let mut first := true
  -- for {env, currNamespace, openDecls, ..} in moduleStx, stx in leadingUpdated do
  --   if first then first := false else IO.print "\n"
  --   let _ ← printCommands stx |>.toIO {fileName, fileMap := FileMap.ofString input, currNamespace, openDecls} {env}
