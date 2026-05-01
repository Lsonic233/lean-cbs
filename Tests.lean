import LeanCbs
open Lean (Json)

-- ─────────────────────────────────────────────────────────────────────────────
-- Minimal test harness
-- ─────────────────────────────────────────────────────────────────────────────

private structure TestState where
  passed : Nat := 0
  failed : Nat := 0

private def TestState.record (s : TestState) (ok : Bool) (label : String) : IO TestState := do
  if ok then
    IO.println s!"  ✓  {label}"
    return { s with passed := s.passed + 1 }
  else
    IO.println s!"  ✗  {label}"
    return { s with failed := s.failed + 1 }

-- Expect parseAndVerify to succeed
private def expectOk (env : CapEnv) (m : ResolveMap) (json : String)
    (label : String) (s : TestState) : IO TestState :=
  match Json.parse json with
  | .error _ => s.record false s!"[json parse fail] {label}"
  | .ok j =>
      s.record (parseAndVerify env m j).isOk label

-- Expect parseAndVerify to fail with a specific ParseError constructor
private def expectErr (env : CapEnv) (m : ResolveMap) (json : String)
    (check : ParseError → Bool) (label : String) (s : TestState) : IO TestState :=
  match Json.parse json with
  | .error _ => s.record false s!"[json parse fail] {label}"
  | .ok j =>
      match parseAndVerify env m j with
      | .ok _  => s.record false label
      | .error e => s.record (check e) label

-- Expect parseAndVerify to succeed AND the program to execute without cap error
private def expectRuns (env : CapEnv) (m : ResolveMap) (json : String)
    (label : String) (s : TestState) : IO TestState := do
  match Json.parse json with
  | .error _ => s.record false s!"[json parse fail] {label}"
  | .ok j =>
      match parseAndVerify env m j with
      | .error _ => s.record false label
      | .ok vp =>
          let result ← CapM.runSafe env vp.prog vp.hSafe
          s.record result.isOk label

-- ─────────────────────────────────────────────────────────────────────────────
-- Capability environment helpers
-- ─────────────────────────────────────────────────────────────────────────────

private def mkEnv : CapEnv := { nextId := 0, wallet := [], revoked := [] }

-- ─────────────────────────────────────────────────────────────────────────────
-- Test suites
-- ─────────────────────────────────────────────────────────────────────────────

-- Suite 1 ─ Basic operations with a read-write-delete environment
def suite_basic (s : TestState) : IO TestState := do
  IO.println "\n── Suite 1: Basic operations ──────────────────────────────────────"
  let tmpdir : System.FilePath := "test_tmp"
  IO.FS.createDirAll tmpdir
  IO.FS.writeFile (tmpdir / "a.txt") "hello\n"
  IO.FS.writeFile (tmpdir / "trash.txt") "bye\n"

  let (rCap, e1) := mkEnv.issue (.file "test_tmp/a.txt") .read
  let (wCap, e2) := e1.issue    (.file "test_tmp/b.txt") .write
  let (dCap, env) := e2.issue   (.file "test_tmp/trash.txt") .delete
  let m : ResolveMap := [("r", rCap), ("w", wCap), ("d", dCap)]

  let s ← expectRuns env m
    "{\"kind\":\"read\",\"capability\":\"r\"}"
    "read a.txt" s
  let s ← expectRuns env m
    "{\"kind\":\"write\",\"capability\":\"w\",\"contents\":\"written\\n\"}"
    "write b.txt literal" s
  let s ← expectRuns env m
    "{\"kind\":\"delete\",\"capability\":\"d\"}"
    "delete trash.txt" s
  let s ← expectRuns env m
    ("{\"kind\":\"seq\"," ++
     "\"first\":{\"kind\":\"read\",\"capability\":\"r\"}," ++
     "\"rest\":{\"kind\":\"write\",\"capability\":\"w\",\"contents\":\"seq out\\n\"}}")
    "seq: read then write" s
  return s

-- Suite 2 ─ v1 value binding (let_read → var reference)
def suite_v1 (s : TestState) : IO TestState := do
  IO.println "\n── Suite 2: v1 let_read / var ─────────────────────────────────────"
  let tmpdir : System.FilePath := "test_tmp"
  IO.FS.writeFile (tmpdir / "src.txt") "copy me\n"

  let (rCap, e1) := mkEnv.issue (.file "test_tmp/src.txt") .read
  let (wCap, env) := e1.issue   (.file "test_tmp/dst.txt") .write
  let m : ResolveMap := [("src_r", rCap), ("dst_w", wCap)]

  -- Read src.txt, pipe its contents into dst.txt via a bound variable
  let s ← expectRuns env m
    ("{\"kind\":\"let_read\",\"var\":\"x\",\"capability\":\"src_r\"," ++
     "\"body\":{\"kind\":\"write\",\"capability\":\"dst_w\"," ++
     "\"contents\":{\"kind\":\"var\",\"name\":\"x\"}}}")
    "let_read: copy src → dst" s

  -- Nested let_read: read src twice, write outer binding to dst
  let s ← expectOk env m
    ("{\"kind\":\"let_read\",\"var\":\"outer\",\"capability\":\"src_r\"," ++
     "\"body\":{\"kind\":\"let_read\",\"var\":\"inner\",\"capability\":\"src_r\"," ++
     "\"body\":{\"kind\":\"write\",\"capability\":\"dst_w\"," ++
     "\"contents\":{\"kind\":\"var\",\"name\":\"outer\"}}}}")
    "nested let_read: outer var reaches into inner body" s

  -- Literal write inside a let_read body (binding present but unused)
  let s ← expectOk env m
    ("{\"kind\":\"let_read\",\"var\":\"x\",\"capability\":\"src_r\"," ++
     "\"body\":{\"kind\":\"write\",\"capability\":\"dst_w\"," ++
     "\"contents\":\"literal inside let\"}}")
    "let_read body: literal write (binding unused)" s

  -- seq inside let_read body: both legs use the outer scope
  let s ← expectOk env m
    ("{\"kind\":\"let_read\",\"var\":\"x\",\"capability\":\"src_r\"," ++
     "\"body\":{\"kind\":\"seq\"," ++
     "\"first\":{\"kind\":\"write\",\"capability\":\"dst_w\",\"contents\":{\"kind\":\"var\",\"name\":\"x\"}}," ++
     "\"rest\" :{\"kind\":\"write\",\"capability\":\"dst_w\",\"contents\":\"second write\"}}}")
    "let_read body: seq uses bound var then literal" s

  return s

-- Suite 3 ─ Elaboration errors (caught before proof construction)
def suite_elab_errors (s : TestState) : IO TestState := do
  IO.println "\n── Suite 3: Elaboration errors ─────────────────────────────────────"
  let (rCap, e1) := mkEnv.issue (.file "test_tmp/a.txt") .read
  let (wCap, env) := e1.issue   (.file "test_tmp/b.txt") .write
  let m : ResolveMap := [("r", rCap), ("w", wCap)]

  -- Unknown capability name
  let s ← expectErr env m
    "{\"kind\":\"read\",\"capability\":\"ghost\"}"
    (fun e => match e with | .unknownCap _ => true | _ => false)
    "unknownCap: name not in resolve map" s

  -- Authority mismatch: read cap used for delete
  let s ← expectErr env m
    "{\"kind\":\"delete\",\"capability\":\"r\"}"
    (fun e => match e with | .authorityMismatch _ _ => true | _ => false)
    "authorityMismatch: read cap used for delete" s

  -- Authority mismatch: write cap used as let_read binding source
  let s ← expectErr env m
    ("{\"kind\":\"let_read\",\"var\":\"x\",\"capability\":\"w\"," ++
     "\"body\":{\"kind\":\"write\",\"capability\":\"w\",\"contents\":\"hi\"}}")
    (fun e => match e with | .authorityMismatch _ _ => true | _ => false)
    "authorityMismatch: write cap used in let_read" s

  -- Authority mismatch: read cap used for write
  let s ← expectErr env m
    "{\"kind\":\"write\",\"capability\":\"r\",\"contents\":\"oops\"}"
    (fun e => match e with | .authorityMismatch _ _ => true | _ => false)
    "authorityMismatch: read cap used for write" s

  -- Unbound variable in write contents
  let s ← expectErr env m
    "{\"kind\":\"write\",\"capability\":\"w\",\"contents\":{\"kind\":\"var\",\"name\":\"y\"}}"
    (fun e => match e with | .unboundVar _ => true | _ => false)
    "unboundVar: var 'y' not in scope" s

  -- Unbound variable inside a let_read body that binds a DIFFERENT name
  let s ← expectErr env m
    ("{\"kind\":\"let_read\",\"var\":\"x\",\"capability\":\"r\"," ++
     "\"body\":{\"kind\":\"write\",\"capability\":\"w\"," ++
     "\"contents\":{\"kind\":\"var\",\"name\":\"z\"}}}")
    (fun e => match e with | .unboundVar _ => true | _ => false)
    "unboundVar: var 'z' not in scope (only 'x' bound)" s

  -- Var from let_read does NOT escape into sibling seq leg
  let s ← expectErr env m
    ("{\"kind\":\"seq\"," ++
     "\"first\":{\"kind\":\"let_read\",\"var\":\"x\",\"capability\":\"r\"," ++
     "            \"body\":{\"kind\":\"write\",\"capability\":\"w\",\"contents\":\"ok\"}}," ++
     "\"rest\":{\"kind\":\"write\",\"capability\":\"w\"," ++
     "          \"contents\":{\"kind\":\"var\",\"name\":\"x\"}}}")
    (fun e => match e with | .unboundVar _ => true | _ => false)
    "scope isolation: binding from seq-first does not leak into seq-rest" s

  return s

-- Suite 4 ─ Wallet validity (lower-level env checks)
def suite_wallet (s : TestState) : IO TestState := do
  IO.println "\n── Suite 4: Wallet / env validity ──────────────────────────────────"
  -- Issue a cap into env₁; mkEnv (empty wallet) has never seen that cap.
  let (capA, env₁) := mkEnv.issue (.file "test_tmp/a.txt") .read
  let m : ResolveMap := [("r", capA)]

  -- Verified in env₁ (capA is in its wallet) → ok
  let s ← expectOk env₁ m
    "{\"kind\":\"read\",\"capability\":\"r\"}"
    "cap in wallet: ok" s

  -- Verified against the empty wallet (capA was never issued there) → invalidCap
  let s ← expectErr mkEnv m
    "{\"kind\":\"read\",\"capability\":\"r\"}"
    (fun e => match e with | .invalidCap _ => true | _ => false)
    "cap not in wallet: invalidCap" s

  return s

-- Suite 5 ─ Prompt injection: restricted env rejects attacker-injected JSON
def suite_injection (s : TestState) : IO TestState := do
  IO.println "\n── Suite 5: Prompt injection ────────────────────────────────────────"
  IO.FS.createDirAll "test_tmp"
  IO.FS.writeFile "test_tmp/sensitive.txt" "TOP SECRET\n"

  -- Orchestrator issues ONLY read + write. No delete, no cap for sensitive.txt.
  let (rCap, e1) := mkEnv.issue (.file "test_tmp/a.txt") .read
  let (wCap, env) := e1.issue   (.file "test_tmp/b.txt") .write
  let m : ResolveMap := [("r", rCap), ("w", wCap)]

  -- Attacker fabricates a delete cap name
  let s ← expectErr env m
    "{\"kind\":\"delete\",\"capability\":\"sensitive_delete\"}"
    (fun e => match e with | .unknownCap _ => true | _ => false)
    "injection: fabricated delete cap rejected" s

  -- Attacker re-uses the read cap name for a delete
  let s ← expectErr env m
    "{\"kind\":\"delete\",\"capability\":\"r\"}"
    (fun e => match e with | .authorityMismatch _ _ => true | _ => false)
    "injection: read cap used for delete rejected (authority mismatch)" s

  -- Attacker fabricates a read cap for sensitive.txt
  let s ← expectErr env m
    "{\"kind\":\"read\",\"capability\":\"secrets_read\"}"
    (fun e => match e with | .unknownCap _ => true | _ => false)
    "injection: fabricated read cap for sensitive.txt rejected" s

  -- Full injected payload: seq(delete, read) — fails at first unknown cap
  let s ← expectErr env m
    ("{\"kind\":\"seq\"," ++
     "\"first\":{\"kind\":\"delete\",\"capability\":\"sensitive_delete\"}," ++
     "\"rest\":{\"kind\":\"read\",\"capability\":\"secrets_read\"}}")
    (fun e => match e with | .unknownCap _ => true | _ => false)
    "injection: full payload (seq delete+read) rejected" s

  -- Confirm sensitive.txt survived untouched
  let contents ← IO.FS.readFile "test_tmp/sensitive.txt"
  let s ← s.record (contents == "TOP SECRET\n")
    "sensitive.txt untouched after all injection attempts"

  return s

-- ─────────────────────────────────────────────────────────────────────────────
-- Entry point
-- ─────────────────────────────────────────────────────────────────────────────

private def allSuites : List (String × String × (TestState → IO TestState)) :=
  [ ("basic",     "Basic read / write / delete / seq",          suite_basic)
  , ("v1",        "v1 let_read / var value binding",            suite_v1)
  , ("elab",      "Elaboration errors (unknownCap, mismatch…)", suite_elab_errors)
  , ("wallet",    "Wallet validity and revocation",             suite_wallet)
  , ("injection", "Prompt-injection attack scenarios",          suite_injection)
  ]

private def printUsage : IO Unit := do
  IO.println "Usage: lake exe lean-cbs-tests [suite]"
  IO.println ""
  IO.println "  (no argument)   run all suites"
  for (name, desc, _) in allSuites do
    IO.println s!"  {name}   {desc}"

def main (args : List String) : IO Unit := do
  -- IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  -- IO.println "  lean-cbs test suite"
  -- IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  let suites : List (TestState → IO TestState) ←
    match args with
    | [] => pure (allSuites.map (·.2.2))
    | [name] =>
        match allSuites.find? (fun (n, _, _) => n == name) with
        | some (_, _, fn) => pure [fn]
        | none =>
            IO.println s!"Unknown suite '{name}'.\n"
            printUsage
            IO.Process.exit 1
    | _ =>
        IO.println "Too many arguments.\n"
        printUsage
        IO.Process.exit 1

  let s : TestState := {}
  let s ← List.foldlM (fun acc fn => fn acc) s suites

  IO.println s!"\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"  {s.passed} passed   {s.failed} failed"
  IO.println  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  if s.failed > 0 then
    IO.Process.exit 1
