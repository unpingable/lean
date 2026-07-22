/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Compiled declaration census for the provisional PJ Tranche-A candidate.

  Output is JSON Lines. Types and values are serialized after erasing
  metadata, alpha-irrelevant binder names, and source universe-parameter
  names. The resulting manifest is sensitive to declaration content rather
  than presentation-only binder spelling.
-/

import Lean
import Lean.Util.CollectAxioms
import PJ
import PJ.HeldOut.StaticRole

open Lean

namespace PJTrancheADeclarationDump

def selectedModules : Array Name := #[
  `PJ.Core,
  `PJ.Hostile,
  `PJ.Instances.GovernedTransport,
  `PJ.Instances.ExecutionCustody,
  `PJ.Instances.SomeoneContinuity,
  `PJ.HeldOut.StaticRole
]

def canonicalLevelParamName (index : Nat) : Name :=
  Name.mkNum `_pj_tranche_a_universe index

def canonicalLevelNameAux
    (parameters : List Name) (name : Name) (index : Nat) : Name :=
  match parameters with
  | [] => name
  | parameter :: rest =>
      if parameter == name then canonicalLevelParamName index
      else canonicalLevelNameAux rest name (index + 1)

def canonicalLevelName (parameters : List Name) (name : Name) : Name :=
  canonicalLevelNameAux parameters name 0

partial def canonicalLevel (parameters : List Name) : Level → Level
  | .zero => .zero
  | .succ level => .succ (canonicalLevel parameters level)
  | .max left right =>
      .max (canonicalLevel parameters left) (canonicalLevel parameters right)
  | .imax left right =>
      .imax (canonicalLevel parameters left) (canonicalLevel parameters right)
  | .param name => .param (canonicalLevelName parameters name)
  | .mvar id => .mvar id

/-- Erase metadata and alpha-irrelevant binder names before serialization. -/
partial def canonicalExpr (levelParameters : List Name) : Expr → Expr
  | .bvar index => .bvar index
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort level => .sort (canonicalLevel levelParameters level)
  | .const name levels =>
      .const name (levels.map (canonicalLevel levelParameters))
  | .app fn arg =>
      .app (canonicalExpr levelParameters fn) (canonicalExpr levelParameters arg)
  | .lam _ binderType body binderInfo =>
      .lam .anonymous (canonicalExpr levelParameters binderType)
        (canonicalExpr levelParameters body) binderInfo
  | .forallE _ binderType body binderInfo =>
      .forallE .anonymous (canonicalExpr levelParameters binderType)
        (canonicalExpr levelParameters body) binderInfo
  | .letE _ type value body nondep =>
      .letE .anonymous (canonicalExpr levelParameters type)
        (canonicalExpr levelParameters value)
        (canonicalExpr levelParameters body) nondep
  | .lit literal => .lit literal
  | .mdata _ expr => canonicalExpr levelParameters expr
  | .proj typeName index struct =>
      .proj typeName index (canonicalExpr levelParameters struct)

def exprString (parameters : List Name) (expr : Expr) : String :=
  reprStr (canonicalExpr parameters expr)

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def jsonStrings (values : List String) : Json :=
  .arr (values.toArray.map Json.str)

def optionalExprJson (parameters : List Name) : Option Expr → Json
  | none => .null
  | some expr => .str (exprString parameters expr)

run_cmd do
  let env ← getEnv
  for moduleName in selectedModules do
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError "selected PJ module is absent: {moduleName}"
    let mut declarations : Array (Name × ConstantInfo) := #[]
    for (name, info) in env.constants do
      if env.getModuleIdxFor? name == some moduleIdx then
        declarations := declarations.push (name, info)
    declarations := declarations.qsort fun left right =>
      left.1.toString < right.1.toString
    for (name, info) in declarations do
      if info.type.hasFVar || info.type.hasExprMVar || info.type.hasLevelMVar then
        throwError "declaration type is not closed: {name}"
      if let some value := info.value? true then
        if value.hasFVar || value.hasExprMVar || value.hasLevelMVar then
          throwError "declaration value is not closed: {name}"
      let axioms ← collectAxioms name
      let axiomNames := (axioms.toList.map Name.toString).mergeSort
      IO.println <| Json.compress <| Json.mkObj [
        ("schema", "pj-tranche-a-compiled-declaration-v1"),
        ("serialization", "lean-4.29-repr-alpha-level-canonical-v1"),
        ("module", moduleName.toString),
        ("name", name.toString),
        ("kind", constantKind info),
        ("type", exprString info.levelParams info.type),
        ("value", optionalExprJson info.levelParams (info.value? true)),
        ("axioms", jsonStrings axiomNames)
      ]

end PJTrancheADeclarationDump
