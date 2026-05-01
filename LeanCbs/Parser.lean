import LeanCbs.Core
import Lean.Data.Json
open Lean (Json)

inductive Contents where
  | lit (s : String)
  | var (name : String)
  deriving Repr
/-
  DSL AST : Intermediate form between raw JSON and a verified CapM program.
-/
inductive DslNode where
  | read (capName : String)
  | write (capName : String) (contents : Contents)
  | delete (capName : String)
  | seq (first rest : DslNode)
  | letRead (varName capName : String) (body : DslNode)
  deriving Repr

abbrev Scope := List String

inductive RContents (sc : Scope) where
  | lit (s : String)
  | var (idx : Fin sc.length)

inductive Resolved : Scope → Type where
  | read    (c : Cap) : Resolved sc
  | write   (c : Cap) (contents : RContents sc) : Resolved sc
  | delete  (c : Cap) : Resolved sc
  | seq     (first rest : Resolved sc) : Resolved sc
  | letRead (c : Cap) (body : Resolved (name :: sc)) : Resolved sc

/-
  Parser Errors
-/
inductive ParseError where
  | malformed (msg  : String)
  | unknownKind (kind : String)
  | missingField (field : String)
  | unknownCap (name : String)
  | invalidCap (name : String)
  | unboundVar (name : String)
  | authorityMismatch (name : String) (expected : Authority)
  deriving Repr

instance : Inhabited ParseError := ⟨.malformed ""⟩

/-
  ResolveMap
-/

abbrev ResolveMap := List (String × Cap)

def ResolveMap.lookup (m : ResolveMap) (name : String) : Option Cap :=
  m.find? (fun p => p.1 == name) |>.map Prod.snd

structure VerifiedProg (env : CapEnv) : Type 1 where
  α : Type
  prog : CapM α
  hSafe : SafeProg env prog

/-
  JSON -> DSL Schema Validation
-/

private def getStrField (j : Json) (field : String) : Except ParseError String :=
  match j.getObjVal? field with
  | .error _ => .error (.missingField field)
  | .ok (.str s) => .ok s
  | .ok _ => .error (.malformed s!"field '{field}' is not a string")

private def getObjField (j : Json) (field : String) : Except ParseError Json :=
  match j.getObjVal? field with
  | .error _ => .error (.missingField field)
  | .ok v => .ok v

private def parseContents (j : Json) (field : String) : Except ParseError Contents :=
  match j.getObjVal? field with
  | .error _ => .error (.missingField field)
  | .ok (.str s) => .ok (.lit s)
  | .ok obj =>
    match obj.getObjVal? "kind" with
    | .ok (.str "var") =>
      match obj.getObjVal? "name" with
      | .ok (.str name) => .ok (.var name)
      | _ => .error (.missingField "name")
    | .ok _ => .error (.unknownKind "contents.kind")
    | .error _ => .error (.missingField "kind")

partial def parseDsl (j : Json) : Except ParseError DslNode := do
  let kind ← getStrField j "kind"
  match kind with
  | "read" =>
      let cap ← getStrField j "capability"
      return .read cap
  | "write" =>
      let cap ← getStrField j "capability"
      let contents ← parseContents j "contents"
      return .write cap contents
  | "delete" =>
      let cap ← getStrField j "capability"
      return .delete cap
  | "seq" =>
      let firstJ ← getObjField j "first"
      let restJ  ← getObjField j "rest"
      let first ← parseDsl firstJ
      let rest  ← parseDsl restJ
      return .seq first rest
  | "let_read" =>
      let varName ← getStrField j "var"
      let capName ← getStrField j "capability"
      let bodyJ ← getObjField j "body"
      let body ← parseDsl bodyJ
      return .letRead varName capName body
  | other => .error (.unknownKind other)

/-
  Pass 2 helpers
-/

/-
  Look up `name` in `sc`, returning the bound `Fin sc.length` index if found.
  Walks the list and lifts the recursive index through `Fin.succ`, so the
  bound is maintained without any runtime arithmetic.
-/
def Scope.indexOf : (sc : Scope) → String → Option (Fin sc.length)
  | [], _ => none
  | x :: xs, name =>
      if x == name then
        some ⟨0, Nat.succ_pos _⟩
      else
        (Scope.indexOf xs name).map Fin.succ

/-
  Resolve a capability name through the `ResolveMap`, lifting `unknownCap`
  into the `ParseError` channel.
-/
private def resolveCap (m : ResolveMap) (capName : String) : Except ParseError Cap :=
  match m.lookup capName with
  | none => .error (.unknownCap capName)
  | some c => .ok c

/-
  Require that capability `c` carries authority `a`, otherwise emit a
  structured `authorityMismatch` error tagged with the original DSL name.
-/
private def requireAuthority (c : Cap) (a : Authority) (capName : String) :
    Except ParseError Unit :=
  if c.authority = a then .ok ()
  else .error (.authorityMismatch capName a)

/-
  Pass 2 — `elaborate`.

  `elaborate m sc node` performs:
    - capability resolution (DslNode names → Cap tokens)
    - authority checking (each leaf's authority matches its node kind)
    - variable resolution (var names → `Fin sc.length` indices)
    - scope threading (letRead extends sc; seq does NOT)

  No proof construction here.
-/
def elaborate (m : ResolveMap) :
    (sc : Scope) → DslNode → Except ParseError (Resolved sc)
  | _,  .read capName => do
      let c ← resolveCap m capName
      let _ ← requireAuthority c .read capName
      return .read c
  | _,  .write capName (.lit s) => do
      let c ← resolveCap m capName
      let _ ← requireAuthority c .write capName
      return .write c (.lit s)
  | sc, .write capName (.var name) => do
      let c ← resolveCap m capName
      let _ ← requireAuthority c .write capName
      match Scope.indexOf sc name with
      | none     => .error (.unboundVar name)
      | some idx => return .write c (.var idx)
  | _,  .delete capName => do
      let c ← resolveCap m capName
      let _ ← requireAuthority c .delete capName
      return .delete c
  | sc, .seq first rest => do
      -- Same `sc` for both legs: bindings from `first` do NOT escape into `rest`.
      let rFirst ← elaborate m sc first
      let rRest  ← elaborate m sc rest
      return .seq rFirst rRest
  | sc, .letRead varName capName body => do
      let c ← resolveCap m capName
      let _ ← requireAuthority c .read capName
      -- Body sees an extended scope: `varName :: sc`.
      let rBody ← elaborate m (varName :: sc) body
      return .letRead c rBody

-- maps each in-scope variable index to its runtime String
abbrev ContextValues (sc : Scope) := Fin sc.length → String

structure VerifiedProgOf (env : CapEnv) (α : Type) where
  prog  : CapM α
  hSafe : SafeProg env prog
/-
  Pass 3(SafeProg Proof Construction) : Final pass in the parsing pipeline.
  Receives a `Resolved sc` where all the hard checking is done.
  Returns a function `ContextValues sc → VerifiedProgOf env α`, since there
  are variables whose runtime values are not known yet.

-/
def lower (env : CapEnv) {sc : Scope} : Resolved sc →
    Option (Σ α : Type, ContextValues sc → VerifiedProgOf env α)
  | .read c =>
      if h : env.valid c then
        if ha : c.authority = .read then
          some ⟨String, fun _ => ⟨CapM.read c, SafeProg.readSafe env c h ha⟩⟩
        else none
      else none
  | .write c (.lit s) =>
      if h : env.valid c then
        if ha : c.authority = .write then
          some ⟨Unit, fun _ => ⟨CapM.write c s, SafeProg.writeSafe env c s h ha⟩⟩
        else none
      else none
  | .write c (.var idx) =>
      if h : env.valid c then
        if ha : c.authority = .write then
          -- vs : Fin sc.length → String, idx : Fin sc.length, so `vs idx` is a plain call
          some ⟨Unit, fun vs => ⟨CapM.write c (vs idx),
                                  SafeProg.writeSafe env c (vs idx) h ha⟩⟩
        else none
      else none
  | .delete c =>
      if h : env.valid c then
        if ha : c.authority = .delete then
          some ⟨Unit, fun _ => ⟨CapM.delete c, SafeProg.deleteSafe env c h ha⟩⟩
        else none
      else none
  | .seq first rest =>
      match lower env first, lower env rest with
      | some ⟨_, va⟩, some ⟨β, vb⟩ =>
          -- result type is `rest`'s; `first`'s value is discarded with `fun _ =>`
          some ⟨β, fun vs =>
            ⟨(va vs).prog.flatMap (fun _ => (vb vs).prog),
             SafeProg.flatMapSafe env (va vs).prog (va vs).hSafe
               (fun _ => (vb vs).hSafe)⟩⟩
      | _, _ => none
  | .letRead c body =>
      if h : env.valid c then
        if ha : c.authority = .read then
          -- Recurse on body under the extended scope (name :: sc).
          -- bodyFn : ContextValues (name :: sc) → VerifiedProgOf env β
          match lower env body with
          | none => none
          | some ⟨β, bodyFn⟩ =>
              -- Fin.cases s vs : Fin (sc.length + 1) → String prepends `s` to `vs`.
              -- This is the extended context for the body under scope (name :: sc).
              -- flatMapSafe's h2 requires `∀ s, SafeProg env (f s)` — satisfied here
              -- because SafeProg never inspects the string value itself.
              some ⟨β, fun vs =>
                ⟨(CapM.read c).flatMap (fun s => (bodyFn (Fin.cases s vs)).prog),
                 SafeProg.flatMapSafe env (CapM.read c)
                   (SafeProg.readSafe env c h ha)
                   (fun s => (bodyFn (Fin.cases s vs)).hSafe)⟩⟩
        else none
      else none

def parseAndVerify (env : CapEnv) (m : ResolveMap) (j : Json) :
    Except ParseError (VerifiedProg env) :=
  match parseDsl j with
  | .error e => .error e
  | .ok node =>
      match elaborate m [] node with
      | .error e => .error e
      | .ok resolved =>
          match lower env resolved with
          | none          => .error (.invalidCap "<post-elaboration>")
          | some ⟨α, fn⟩ =>
              let vp := fn (fun i => i.elim0)
              .ok ⟨α, vp.prog, vp.hSafe⟩
