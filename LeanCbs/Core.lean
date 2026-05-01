import Lean
open IO FS System

/- ===========================================================
   Basic types
   =========================================================== -/

inductive Resource where
  | file : String → Resource  -- identified by path
  deriving DecidableEq, Repr

inductive Authority where
  | read
  | write
  | delete
  deriving DecidableEq, Repr

/-
unique identifier per capability token
-/
abbrev CapId := Nat

structure Cap where
  private mk ::
  resource : Resource
  authority : Authority
  identity : CapId
  deriving DecidableEq, Repr

inductive CapError where
  | invalidCap : CapId → CapError
  | wrongAuthority : CapError
  deriving Repr

/- ===========================================================
   The free monad CapM
   =========================================================== -/

inductive CapCmd : Type → Type where
  | read : Cap → CapCmd String
  | write : Cap → String → CapCmd Unit
  | delete : Cap → CapCmd Unit

inductive CapM : Type → Type _ where
  | pure : α → CapM α
  | cons : CapCmd β → (β → CapM α) → CapM α

def CapM.flatMap {α β : Type} (f : α → CapM β) : CapM α → CapM β
  | .pure a => f a
  | .cons cmd k => .cons cmd (fun b => (k b).flatMap f)

instance : Monad CapM where
  pure := CapM.pure
  bind x f := CapM.flatMap f x

def CapM.read (c : Cap) : CapM String := .cons (CapCmd.read c) .pure
def CapM.write (c : Cap) (s : String) : CapM Unit := .cons (CapCmd.write c s) .pure
def CapM.delete (c : Cap) : CapM Unit := .cons (CapCmd.delete c) .pure

/- ===========================================================
   The capability environment
   =========================================================== -/

/-
Each agent has a list of held capabilities
-/
structure CapEnv where
  nextId : CapId -- every issued cap gets a new Id
  wallet : List Cap -- a capability is valid IFF it is present here. Revoking means removing from here.
  revoked : List CapId -- ids that have been invalidated since issuance

/-
Held Predicate for checking for membership
-/
def CapEnv.valid (env : CapEnv) (c : Cap) : Prop :=
  c ∈ env.wallet

instance (env : CapEnv) (c : Cap) : Decidable (env.valid c) :=
  inferInstanceAs (Decidable (c ∈ env.wallet))

/-
  checks if capability c is in the wallet.
-/
def CapEnv.isValid (env : CapEnv) (c : Cap) : Bool :=
  env.wallet.any (fun c' => c'.identity == c.identity)

/-
Bridge lemma: `env.valid c` (the `Prop` used by `SafeProg`) implies
`env.isValid c = true` (the `Bool` consulted by the interpreter).
-/
theorem CapEnv.isValid_of_valid {env : CapEnv} {c : Cap}
    (h : env.valid c) : env.isValid c = true := by
  show env.wallet.any (fun c' => c'.identity == c.identity) = true
  rw [List.any_eq_true]
  exact ⟨c, h, by simp⟩

def CapEnv.issue (env : CapEnv) (r : Resource) (a : Authority) : Cap × CapEnv :=
  let cap : Cap := {resource := r, authority := a, identity := env.nextId}
  (cap, {env with
    nextId := env.nextId + 1
    wallet := cap :: env.wallet
    revoked := env.revoked
    })

/- ===========================================================
   Safety predicate
   =========================================================== -/

inductive SafeProg : {α : Type} → CapEnv → CapM α → Prop where
  | pureSafe (env : CapEnv) (a : α) : SafeProg env (CapM.pure a)
  | readSafe (env : CapEnv) (c : Cap)
      (hv : env.valid c)
      (ha : c.authority = .read) :
      SafeProg env (CapM.read c)
  | writeSafe (env : CapEnv) (c : Cap) (s : String)
      (hv : env.valid c)
      (ha : c.authority = .write):
      SafeProg env (CapM.write c s)
  | deleteSafe (env : CapEnv) (c : Cap)
      (hv : env.valid c)
      (ha : c.authority = .delete) :
      SafeProg env (CapM.delete c)
  | flatMapSafe (env : CapEnv) (x : CapM α)
      (h1 : SafeProg env x)
      (h2 : ∀ a, SafeProg env (f a)) :
      SafeProg env (CapM.flatMap f x)

theorem SafeProg.mono_wallet {α : Type} {env₁ env₂ : CapEnv} {prog : CapM α}
    (hsub : env₁.wallet ⊆ env₂.wallet)
    (h : SafeProg env₁ prog) :
    SafeProg env₂ prog := by
      induction h with
      | pureSafe env₁ a => exact SafeProg.pureSafe env₂ a
      | readSafe _ c hv ha => exact SafeProg.readSafe env₂ c (hsub hv) ha
      | writeSafe _ c s hv ha => exact SafeProg.writeSafe env₂ c s (hsub hv) ha
      | deleteSafe _ c hv ha => exact SafeProg.deleteSafe env₂ c (hsub hv) ha
      | flatMapSafe _ x _ _ ih1 ih2 =>
          exact SafeProg.flatMapSafe env₂ x (ih1 hsub) (fun a => ih2 a hsub)
