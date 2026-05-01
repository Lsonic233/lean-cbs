import LeanCbs.Core
open IO FS System

def CapEnv.revoke (env : CapEnv) (id : CapId): CapEnv :=
  { nextId := env.nextId,
    wallet := env.wallet.filter (fun c => c.identity ≠ id)
    revoked := env.revoked ++ [id]
  }

/-
Looks at one command and decides whether that command is allowed under
the current capability environment.
-/
def CapCmd.check (env : CapEnv) : {β : Type} → CapCmd β → Except CapError Unit
  | _, .read c =>
      if !env.isValid c then .error (.invalidCap c.identity)
      else if c.authority != .read then .error .wrongAuthority
      else .ok ()
  | _, .write c _ =>
      if !env.isValid c then .error (.invalidCap c.identity)
      else if c.authority != .write then .error .wrongAuthority
      else .ok ()
  | _, .delete c =>
      if !env.isValid c then .error (.invalidCap c.identity)
      else if c.authority != .delete then .error .wrongAuthority
      else .ok ()


/-
`AllSafe env prog` says that every command anywhere in `prog` (head, and all
continuations after every possible runtime input) passes `CapCmd.check`.
The `cons` case carries `∀ b, AllSafe env (k b)` — universal over the
continuation's input, exactly because we cannot inspect runtime values
at proof time.
-/
inductive AllSafe (env : CapEnv) : {α : Type} → CapM α → Prop where
  | pure {α : Type} (a : α) : AllSafe env (CapM.pure a)
  | cons {α β : Type} (cmd : CapCmd β) (k : β → CapM α)
      (hcheck : CapCmd.check env cmd = .ok ())
      (hk : ∀ b, AllSafe env (k b)) :
      AllSafe env (CapM.cons cmd k)

/-
`AllSafe` is preserved by `flatMap`: if every reachable command in `x`
checks and every reachable command in every `f a` checks, then so does
every reachable command in `x.flatMap f`.
-/
theorem AllSafe.flatMap {α β : Type} {env : CapEnv} {x : CapM α}
    {f : α → CapM β} (hx : AllSafe env x)
    (hf : ∀ a, AllSafe env (f a)) :
    AllSafe env (x.flatMap f) := by
  induction hx with
  | pure a =>
      -- (.pure a).flatMap f = f a
      exact hf a
  | cons cmd k hcheck _ ihk =>
      -- (.cons cmd k).flatMap f = .cons cmd (fun b => (k b).flatMap f)
      exact AllSafe.cons cmd _ hcheck (fun b => ihk b)

/-
Soundness theorem : `SafeProg env prog` implies every reachable
command of `prog` passes the cap check.
-/
theorem SafeProg.allSafe {α : Type} {env : CapEnv} {prog : CapM α}
    (h : SafeProg env prog) : AllSafe env prog := by
  induction h with
  | pureSafe _ a => exact AllSafe.pure a
  | readSafe _ c hv ha =>
      unfold CapM.read
      refine AllSafe.cons (CapCmd.read c) CapM.pure ?_ ?_
      · simp [CapCmd.check, CapEnv.isValid_of_valid hv, ha]
      · intro b; exact AllSafe.pure b
  | writeSafe _ c s hv ha =>
      unfold CapM.write
      refine AllSafe.cons (CapCmd.write c s) CapM.pure ?_ ?_
      · simp [CapCmd.check, CapEnv.isValid_of_valid hv, ha]
      · intro b; exact AllSafe.pure b
  | deleteSafe _ c hv ha =>
      unfold CapM.delete
      refine AllSafe.cons (CapCmd.delete c) CapM.pure ?_ ?_
      · simp [CapCmd.check, CapEnv.isValid_of_valid hv, ha]
      · intro b; exact AllSafe.pure b
  | flatMapSafe _ _ _ _ ih1 ih2 =>
      exact AllSafe.flatMap ih1 ih2


/-
`CapM.run` is the actual interpreter function that makes the filesystem calls
-/
def CapM.run (env : CapEnv) : CapM α → IO (Except CapError α)
  | .pure a => return .ok a
  | .cons cmd k =>
    match CapCmd.check env cmd with
    | .error e => return .error e
    | .ok _ =>
      match cmd with
      | .read c =>
        match c.resource with
        | .file path => do
          let contents ← IO.FS.readFile path
          CapM.run env (k contents)
      | .write c s =>
        match c.resource with
        | .file path => do
          IO.FS.writeFile path s
          CapM.run env (k ())
      | .delete c =>
        match c.resource with
        | .file path => do
          IO.FS.removeFile path
          CapM.run env (k ())
/-
  Same interpreter function as above but has a proof obligation.
-/
def CapM.runSafe (env : CapEnv) (prog : CapM α) (_h : SafeProg env prog) :
    IO (Except CapError α) :=
  CapM.run env prog
