# EVM bytecode semantics: notes

## Phase 1: what exists

- `Evm/State.lean`: `EvmState` (`pc : Nat`, `stack : List Word` with the top of the stack at the
  head, `memory : ByteArray`). `Context` holds `code`, `env` and the `jumpdests` table, built
  once by a linear scan that skips `PUSHn` immediates.
- `Evm/Step.lean`: `decode : UInt8 → Option Op`, `exec : Context → EvmState → Op → HostM EvmState`,
  and `step : Context → EvmState → HostM (IterStep EvmState Empty)`.
- `Evm/Run.lean`: `Evm.run code env : HostM Empty := CoFree.iter EvmState.initial (step ..)`.
- `EvmTests/Host.lean`: a test host. It runs `CoFree.runM` over
  `ExceptT Stop (StateM Storage)`: `sload`/`sstore` use a threaded map, `halt` throws, and every
  other op is `unsupported`.
- `EvmTests/Basic.lean`: hand-assembled programs. They are checked with `#guard`, and five of them
  are also proved with `decide +kernel`. `Evm.run` reduces in the kernel, so facts about concrete
  programs can be proved and not only evaluated.

Only standard axioms are used (Audit checks this, now over 98 modules).

## Simplifications

- **Gas is not modelled.** There is no per-opcode cost, no memory-expansion cost and no `GAS`
  opcode, and the `Host.gas` op is never emitted. Out-of-gas cannot happen, except as the
  memory cap below.
- **Memory cap.** A memory access ending above `memoryLimit = 2^32` halts with `.invalid`.
  This stands in for running out of gas on expansion and keeps evaluation finite. An access with
  length 0 touches nothing, whatever its offset (as in the EVM).
- **Every exceptional halt is `.invalid`.** This covers stack underflow, stack overflow
  (> 1024), a bad jump destination, an unsupported or undefined opcode, and the memory cap.
  `SimplifiedOutcome` has no finer exceptional cases. All of these consume all gas in the real
  EVM, so they are indistinguishable once gas is gone.
- **STOP, and running past the end of the code,** give `.ret .empty`.
- **Stack overflow is checked after the instruction,** not before. Only `PUSHn`, `DUPn` and `PC`
  grow the stack, and none of them performs a host operation, so the observable trace is the
  same.
- **The static context is not checked.** `Evm.run` takes no `ExecutionMode`, so `SSTORE` in a
  static frame is allowed (Sir checks it via `Context.checkStateful`).
- **`Env` is carried but unused,** because no environment opcode is in the subset.
- **Memory is a `ByteArray` grown with zeros to a multiple of 32 bytes,** so its size is
  already EVM's `32 * activeWords`, ready for `MSIZE`.
- **`PUSHn` reading past the end of the code** treats the missing bytes as zeros
  (`slicePadded`), as the EVM does.
- **The opcode subset is the one requested.** Everything else, including `GAS`, `CALL` and
  `BALANCE`, decodes to `none` and halts with `.invalid`.

## Changes to existing code

- None to Sir, Host or ITree. Only `lakefile.toml` (two new `lean_lib`s and default targets)
  and `Audit.lean` (imports and the `libs` list) changed.
- I did not factor out op evaluation. `Evm.Step` imports `Sir.Eval` and calls
  `Sir.UnOp.eval`/`Sir.BinOp.eval` directly. Their operand order is already EVM stack order. The
  cost is that the `Evm` lib depends on the `Sir` lib (see open questions).

## Open questions

1. **`Host/Interp.lean` already implements HostE → WorldE** (`hostStep`/`interpHost`), and
   `Sir.Program.run` uses it. `Scratch/Transformers.lean` does not exist in this checkout. Is
   the brief out of date, or is a different handler meant? I left it alone.
2. **Should `Evm` depend on `Sir`?** The other option is to move `UnOp`/`BinOp`/`TernOp`
   and their `eval`s from `Sir/Ir.lean` and `Sir/Eval.lean` into `Host`, which touches Sir.
   Sharing the definitions makes the later SIR↔EVM proof easier either way.
3. **Static mode:** add an `ExecutionMode` (or `static : Bool`) argument to `Evm.run`?
4. **Is the 2^32 memory cap acceptable,** or should out-of-gas be modelled properly?
5. **Test count:** the brief asked for 8–12 tests. There are 12 groups, but about 38 `#guard`
   lines plus 5 kernel proofs. Trim if that is too many.

## Phase 2: EVMYulLean as the reference semantics

Investigated `NethermindEth/EVMYulLean`, `main` at `047f630` (2025-09-24), and
`leonardoalt/evm-smith`.

### Toolchain and dependency

- EVMYulLean pins `leanprover/lean4:v4.22.0` and Mathlib `v4.22.0`. evm-smith pins v4.22.0 too.
  We are on v4.34.1.
- A lake workspace builds with a single toolchain, and Mathlib v4.22 will not build on v4.34.1.
  **So it cannot be added as a lake dependency as it stands.** We would need either a port of
  EVMYulLean (and a Mathlib for v4.34), or a separate package on v4.22 holding the bridge.
- Its lakefile is heavy:
  - Build targets `git clone` two C libraries (sha-2, SHA3IUF) and compile an FFI with `cc`.
  - `extern_lib` also clones `EthereumTests` if it is missing, so the first build needs network
    access.
  - Mathlib roughly multiplies our build time by ten. We currently have no dependencies.
- **Axiom audit:**
  - Upstream has no `axiom` and no `sorry` (grepped, excluding `EthereumTests`).
  - The FFI functions (`keccak256`, `sha256`, `BLAKE2Compress`, `ByteArray.zeroes`) are
    `@[extern] opaque`. Opaque constants are not axioms, so `#audit_axioms` would pass, but
    nothing can be proved about their values. `zeroes` is only used in precompiles and the log
    bloom, not in core memory.
  - `partial def D_J_aux`, the JUMPDEST analysis, is opaque to proofs. Jump lemmas would have to
    take the valid-jump array as a hypothesis or replace `D_J`.
- **evm-smith uses a fork** (`leonardoalt/EVMYulLean`, a submodule; the GitHub URL now
  returns 404). Its `AXIOMS.md` lists two added `axiom`s in `EvmYul/Frame/MutualFrame.lean`:
  `precompile_preserves_accountMap` and `lambda_derived_address_ne_C` (Keccak collision
  resistance). Any proof depending on them would fail our axiom audit. Use upstream, or avoid
  those lemmas.

### Shape of their semantics

- `EVM.State` extends `SharedState` (world state, substate, `ExecutionEnv`, blocks, …, plus
  `MachineState` with `gasAvailable`, `activeWords`, `memory : ByteArray` and `returnData`), and
  adds `pc : UInt256`, `stack : List UInt256` (head is the top) and `execLength`.
- `UInt256` is `structure { val : Fin (2^256) }`, not `BitVec 256`.
- Storage lives inside `accountMap` (an RBMap) under the code owner's account.
- `X fuel validJumps s : Except ExecutionException (ExecutionResult State)` is a
  fuel-indexed loop:
  1. `decode` the instruction.
  2. `Z` checks for an exceptional halt: gas, `δ` (stack inputs), underflow, bad jump, overflow
     (`α`), static violation.
  3. `step` runs the instruction. CALL and CREATE recurse into `Θ`/`Λ` inside a `mutual`
     block, so nested frames are inline. Other opcodes go through `EvmYul.step`, and arithmetic
     uses `execBinOp f`.
  4. `H` decides whether to halt.
- The two main differences from ours:
  - They thread the whole world state explicitly, whereas we perform `HostE` ops.
  - They recurse into nested calls inline, whereas for us a call is one `HostE.call`.

### How to relate the two

1. **Handler.** Write `runY : Nat → HostM Empty → EVM.State → Except ExecutionException Result`.
   It answers `sload`/`sstore` from the code owner's storage in `accountMap` and turns
   `halt o` into a result (like `hostStep`, but over their state). For the subset, only
   `sload`, `sstore` and `halt` are needed.
2. **Relation** `R (s : EvmState) (y : EVM.State)`:
   - `s.pc = y.pc.toNat`.
   - `s.stack.map (·.toNat) = y.stack.map (·.toNat)`.
   - `s.memory.size = 32 * y.activeWords.toNat`.
   - Memory bytes agree, reading past `y.memory.size` as zero.
   - `ctx.code = y.executionEnv.code`.
   - `ctx.jumpdests` agrees with `validJumps`.
   - The handler's storage is `y`'s storage.
3. **Statement (refinement modulo gas).** If `R s y` and `X` does not fail with `OutOfGass`,
   then the outcomes agree, and `.invalid` corresponds to any other `ExecutionException`. We
   prove it one opcode at a time by simulation: one `step` iteration on our side against one `X`
   iteration on theirs.

### Proof plan for ADD

1. **Our side** (in this repo, no new dependency). Assume
   `ctx.code[s.pc]? = some 0x01` and `s.stack = a :: b :: rest`. Then `(step ctx s).observe`
   reaches `.pure (.repeat ⟨s.pc + 1, (a + b) :: rest, s.memory⟩)` through silent steps only,
   with no `HostE` op. This is proved by unfolding `step`/`decode`/`exec`/`pop` and the
   `CoFree.bind` lemmas in `ITree/Machine/Theorems.lean`, with `Skip`/`Same` to drop the silent
   steps.
2. **Their side.** Assume `decode y.code y.pc = some (.ADD, none)`,
   `y.stack = μ₀ :: μ₁ :: rest` and `y.gasAvailable ≥ Gverylow`. Then
   `X (f+1) J y = X f J { y with pc := y.pc + 1, stack := (μ₀ + μ₁) :: rest, gasAvailable -= 3, execLength += 1 }`.
   This is proved by unfolding `Z` (`δ .ADD = some 2`, `α .ADD = some 1`, the jump checks are
   false), then `step` → `EvmYul.step .ADD` → `execBinOp UInt256.add`, with `H` returning `none`.
   `dbg_trace` in `EvmYul.step` is logically the identity.
3. **Word bridge.** `(a + b).toNat = (UInt256.add a' b').val` when `a.toNat = a'.val` and
   `b.toNat = b'.val`: both sides are addition mod 2^256 (`BitVec.toNat_add`, `Fin.val_add`).
4. **Combine.** `R s y` together with 1–3 gives `R s' y'`. The `pc` bound needs
   `y.pc.toNat + 1 < 2^256`, which holds because `pc < code.size`.

The blocker is the toolchain gap, not the proof: steps 2–4 need EVMYulLean's definitions to
elaborate next to ours. Step 1 can be done now. A cheaper first move is to port only the
EVMYulLean files the subset needs (`UInt256`, `Stack`, `Instr`, `execBinOp`, a gas-free `X`)
into a Mathlib-free module on v4.34.1, and check the port against their conformance tests
separately.
