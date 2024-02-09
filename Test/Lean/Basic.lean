import Lean
open Lean

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
partial def elabAexp : Syntax → IO aexp
  -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
  -- `mkNatLit` creates an `Expr` from a `Nat`
  | `(aexp_syn| $n:num) => return aexp.ANum n.getNat
  | `(aexp_syn| $i:ident) => return aexp.AVar i.getId.toString
  | `(aexp_syn| $x:aexp_syn + $y:aexp_syn) => do
    let x ← elabAexp x
    let y ← elabAexp y
    return aexp.AAdd x y
  | _ => throw (IO.userError "not an aexp")

partial def elabBexp : Syntax → IO bexp
  | `(bexp_syn| true) => return bexp.BConst Bool.true
  | `(bexp_syn| false) => return bexp.BConst Bool.false
  | `(bexp_syn| ! $b:bexp_syn) => do
    let b ← elabBexp b
    return bexp.BNot b
  | `(bexp_syn| $x:bexp_syn && $y:bexp_syn) => do
    let x ← elabBexp x
    let y ← elabBexp y
    return bexp.BAnd x y
  | `(bexp_syn| $x:aexp_syn < $y:aexp_syn) => do
    let x ← elabAexp x
    let y ← elabAexp y
    return bexp.BLt x y
  | _ => throw (IO.userError "not a bexp")

partial def elabCom : Syntax → IO com
  | `(com_syn| skip) => return com.CSkip
  | `(com_syn| $x:ident := $n:aexp_syn) => do
    let n ← elabAexp n
    return com.CAsgn x.getId.toString n
  | `(com_syn| $x:com_syn ;; $y:com_syn) => do
    let x ← elabCom x
    let y ← elabCom y
    return com.CSeq x y
  | `(com_syn| if $b:bexp_syn then $x:com_syn else $y:com_syn fi) => do
    let b ← elabBexp b
    let x ← elabCom x
    let y ← elabCom y
    return com.CIf b x y
  | `(com_syn| while $b:bexp_syn do $x:com_syn od) => do
    let b ← elabBexp b
    let x ← elabCom x
    return com.CWhile b x
  | _ => throw (IO.userError "not a com")
end

mutual
def printAexp (a : aexp) : IO Unit :=
  match a with
  | .ANum n => IO.print n
  | .AVar x => IO.print x
  | .AAdd a1 a2 => do
    printAexp a1
    IO.print " + "
    printAexp a2

def printBexp (b : bexp) : IO Unit :=
  match b with
  | .BConst b => IO.print b
  | .BNot b => do
    IO.print "¬ "
    printBexp b
  | .BAnd b1 b2 => do
    printBexp b1
    IO.print " ∧ "
    printBexp b2
  | .BLt a1 a2 => do
    printAexp a1
    IO.print " < "
    printAexp a2

def printCom (c : com) : IO Unit :=
  match c with
  | .CSkip => IO.print "skip"
  | .CAsgn x a => do
    IO.print x
    IO.print " := "
    printAexp a
  | .CSeq c1 c2 => do
    printCom c1
    IO.print " ; "
    printCom c2
  | .CIf b cthen celse => do
    IO.print "if "
    printBexp b
    IO.print " then "
    printCom cthen
    IO.print " else "
    printCom celse
  | .CWhile b c => do
    IO.print "while "
    printBexp b
    IO.print " do "
    printCom c
end
end IMP
