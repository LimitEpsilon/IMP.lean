import Lean
open Lean Elab Command Meta

def hello := "world"

-- syntax (macro; syntax)* elab
-- syntax transforms a String to a Syntax
-- macro transforms a Syntax to a String
-- elab transforms a Syntax to a Expr
syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ _ =>
  Lean.logInfo "finally, blue!"

red

#check TSyntax `term
#check `term

namespace IMP

-- define deep embedding of syntax
mutual
  inductive aexp
  | ANum (n : Nat) : aexp
  | AVar (x : String) : aexp
  | AAdd (n1 n2 : aexp) : aexp

  inductive bexp
  | BConst (b : Bool) : bexp
  | BNot (b : bexp) : bexp
  | BAnd (b1 b2 : bexp) : bexp
  | BLt (a1 a2 : aexp) : bexp

  inductive com
  | CSkip
  | CAsgn (x : String) (n : aexp) : com
  | CSeq (c1 c2 : com) : com
  | CIf (b : bexp) (c1 c2 : com) : com
  | CWhile (b : bexp) (c : com) : com
end

-- define syntactic categories
declare_syntax_cat aexp_syn
declare_syntax_cat bexp_syn
declare_syntax_cat com_syn

-- parsers for aexp
syntax num : aexp_syn
syntax ident : aexp_syn
syntax aexp_syn " + " aexp_syn : aexp_syn

-- parsers for bexp
syntax "true" : bexp_syn
syntax "false" : bexp_syn
syntax "!" bexp_syn : bexp_syn
syntax bexp_syn " && " bexp_syn : bexp_syn
syntax aexp_syn " < " aexp_syn : bexp_syn

-- parsers for com
syntax "skip" : com_syn
syntax ident " := " aexp_syn : com_syn
syntax com_syn " ;; " com_syn : com_syn
syntax "if " bexp_syn "then " com_syn "else " com_syn " fi" : com_syn
syntax "while " bexp_syn "do " com_syn " od" : com_syn

mutual
partial def elabAexp : Syntax → MetaM Expr
  -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
  -- `mkNatLit` creates an `Expr` from a `Nat`
  | `(aexp_syn| $n:num) => mkAppM ``aexp.ANum #[mkNatLit n.getNat]
  | `(aexp_syn| $i:ident) => mkAppM ``aexp.AVar #[mkStrLit i.getId.toString]
  | `(aexp_syn| $x:aexp_syn + $y:aexp_syn) => do
    let x ← elabAexp x
    let y ← elabAexp y
    mkAppM ``aexp.AAdd #[x, y]
  | _ => throwUnsupportedSyntax

partial def elabBexp : Syntax → MetaM Expr
  | `(bexp_syn| true) => mkAppM ``aexp.ANum #[.const ``Bool.true []]
  | `(bexp_syn| false) => mkAppM ``aexp.AVar #[.const ``Bool.false []]
  | `(bexp_syn| ! $b:bexp_syn) => do
    let b ← elabBexp b
    mkAppM ``bexp.BNot #[b]
  | `(bexp_syn| $x:bexp_syn && $y:bexp_syn) => do
    let x ← elabBexp x
    let y ← elabBexp y
    mkAppM ``bexp.BAnd #[x, y]
  | `(bexp_syn| $x:aexp_syn < $y:aexp_syn) => do
    let x ← elabAexp x
    let y ← elabAexp y
    mkAppM ``bexp.BLt #[x, y]
  | _ => throwUnsupportedSyntax

partial def elabCom : Syntax -> MetaM Expr
  | `(com_syn| skip) => mkAppM ``com.CSkip #[]
  | `(com_syn| $x:ident := $n:aexp_syn) => do
    let n ← elabAexp n
    mkAppM ``com.CAsgn #[mkStrLit x.getId.toString, n]
  | `(com_syn| $x:com_syn ;; $y:com_syn) => do
    let x ← elabCom x
    let y ← elabCom y
    mkAppM ``com.CSeq #[x, y]
  | `(com_syn| if $b:bexp_syn then $x:com_syn else $y:com_syn fi) => do
    let b ← elabBexp b
    let x ← elabCom x
    let y ← elabCom y
    mkAppM ``com.CIf #[b, x, y]
  | `(com_syn| while $b:bexp_syn do $x:com_syn od) => do
    let b ← elabBexp b
    let x ← elabCom x
    mkAppM ``com.CWhile #[b, x]
  | _ => throwUnsupportedSyntax
end

elab ">>" p:com_syn "<<" : term => elabCom p

#reduce >>
a := 5;;
if 3 < 4 then
  c := 5
else
  a := a + 1
fi;;
b := 10
<<

end IMP
