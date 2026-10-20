-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MeTTailCore.MeTTaSyntax.Atom

/-!
# LeaTTa atom operations and runtime profile

The atom and payload carriers are owned by the independent shared structure
module. This module adds LeaTTa's numeric equivalence, builtin designators,
meta-type classification and grounded-operation outcomes. Those operations
are an implementation profile, not the authority for HE source judgments.
-/

namespace Metta

namespace Ground

/-- Runtime equality for grounded values. Hyperon's `Number` grounding compares integer and float
values by numeric value, so `1` and `1.0` match even though their constructors differ. -/
def equiv : Ground → Ground → Bool
  | Ground.int a, Ground.float b => Float.ofInt a == b
  | Ground.float a, Ground.int b => a == Float.ofInt b
  | a, b => Ground.beq a b

end Ground

mutual

/-- Runtime equality for atoms. This keeps structural shape but uses `Ground.equiv` for grounded
payloads, matching Hyperon's `gv_eq` for numeric atoms without changing the proof-facing `BEq`. -/
def Atom.equiv : Atom → Atom → Bool
  | Atom.sym a, Atom.sym b => a == b
  | Atom.var a, Atom.var b => a == b
  | Atom.gnd a, Atom.gnd b => Ground.equiv a b
  | Atom.expr a, Atom.expr b => Atom.equivList a b
  | _, _ => false

/-- Pointwise runtime equality of atom lists. -/
def Atom.equivList : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => Atom.equiv x y && Atom.equivList xs ys
  | _, _ => false

end

/-- Coarse meta-types from the current Hyperon specification. -/
inductive MetaType where
  | atom | symbol | variable | expression | grounded | typeType | undefined | errorType
  deriving Repr, BEq, Inhabited

/-- Runtime outcomes returned by grounded operations. -/
inductive ReduceResult where
  | ok : List Atom → ReduceResult
  | noReduce : ReduceResult
  | incorrectArgument : String → ReduceResult
  | runtimeError : String → ReduceResult
  deriving Repr, BEq, Inhabited

namespace Atom

/-- The unit atom `()`: the grounded `Unit`. An assertion succeeds by reducing to it. -/
def unit : Atom := Atom.gnd Ground.unit
/-- The Boolean `True` as a grounded atom. -/
def trueA : Atom := Atom.gnd (Ground.bool true)
/-- The Boolean `False` as a grounded atom. -/
def falseA : Atom := Atom.gnd (Ground.bool false)
/-- The `Empty` symbol: reducing to it prunes the current nondeterministic branch (no results). -/
def empty : Atom := Atom.sym "Empty"
/-- The `NotReducible` marker: a redex that yielded no reduction. -/
def notReducible : Atom := Atom.sym "NotReducible"
/-- The gradual top type `%Undefined%`, compatible with every type on either side of a check. -/
def undefined : Atom := Atom.sym "%Undefined%"
/-- The kind of types, `Type`. -/
def typeSym : Atom := Atom.sym "Type"
/-- The `Atom` meta-type: accepts anything, so quoted/unevaluated arguments stay well-typed. -/
def atomType : Atom := Atom.sym "Atom"
def symbolType : Atom := Atom.sym "Symbol"
def variableType : Atom := Atom.sym "Variable"
def expressionType : Atom := Atom.sym "Expression"
/-- The `Grounded` meta-type (numbers, booleans, grounded operations). -/
def groundedType : Atom := Atom.sym "Grounded"
/-- The `ErrorType` symbol: the type of `(Error …)` atoms. -/
def errorType : Atom := Atom.sym "ErrorType"

/-- True if `a` is an error atom: either an expression headed by `Error` or a grounded
`Ground.error`.  The expression form follows the interpreter specification's `(Error ...)`
pattern, whose tail is not arity-restricted. -/
def isError : Atom → Bool
  | Atom.expr (Atom.sym "Error" :: _) => true
  | Atom.gnd (Ground.error _) => true
  | _ => false

/-- The syntactic meta-type (kind) of an atom: symbol / variable / grounded /
expression.  `Type` and `ErrorType` are ordinary symbol atoms here; their
declared types belong to the type environment, not to syntactic meta-typing. -/
def metaType : Atom → MetaType
  | Atom.sym _ => MetaType.symbol
  | Atom.var _ => MetaType.variable
  | Atom.gnd _ => MetaType.grounded
  | Atom.expr _ => MetaType.expression

/-- The type designator atom for a meta-type (inverse of `metaType` on the built-in type symbols). -/
def typeAtomOfMetaType : MetaType → Atom
  | MetaType.atom => atomType
  | MetaType.symbol => symbolType
  | MetaType.variable => variableType
  | MetaType.expression => expressionType
  | MetaType.grounded => groundedType
  | MetaType.typeType => typeSym
  | MetaType.undefined => undefined
  | MetaType.errorType => errorType

/-- True if `a` is exactly one of the special built-in type designators. -/
def isBuiltinTypeSymbol : Atom → Bool
  | Atom.sym "Type" => true
  | Atom.sym "%Undefined%" => true
  | Atom.sym "Atom" => true
  | Atom.sym "Symbol" => true
  | Atom.sym "Variable" => true
  | Atom.sym "Expression" => true
  | Atom.sym "Grounded" => true
  | Atom.sym "ErrorType" => true
  | _ => false

/-- Function type constructor: `(-> A B C)`. -/
def mkArrow (args : List Atom) (ret : Atom) : Atom := Atom.expr (Atom.sym "->" :: (args ++ [ret]))

def isArrow : Atom → Bool
  | Atom.expr (Atom.sym "->" :: _) => true
  | _ => false

/-- The head (first child) of an expression, or `none` for a non-expression / empty expression. -/
def head? : Atom → Option Atom
  | Atom.expr (x :: _) => some x
  | _ => none

/-- The argument list (children after the head) of an expression, or `none` otherwise. -/
def args? : Atom → Option (List Atom)
  | Atom.expr (_ :: xs) => some xs
  | _ => none

end Atom
end Metta
