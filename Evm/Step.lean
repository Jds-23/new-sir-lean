import Evm.State
import Sir.Eval

/-! Decoding and executing one EVM instruction.

Only a subset of opcodes is supported; every other byte decodes to `none` and halts the frame
with `.invalid`. Arithmetic reuses `Sir.UnOp.eval`/`Sir.BinOp.eval`, whose operands are already
in EVM stack order (the first is the top of the stack). Gas is not modelled. -/

open Host

namespace Evm

/-- The supported instructions. `push n` is `PUSHn` (`n = 0` is `PUSH0`); `dup n` and `swap n`
are `DUPn` and `SWAPn`, `1 ≤ n ≤ 16`. -/
inductive Op
  | stop
  | unop (op : Sir.UnOp)
  | binop (op : Sir.BinOp)
  | pop
  | push (n : Nat)
  | dup (n : Nat)
  | swap (n : Nat)
  | mload | mstore | mstore8
  | sload | sstore
  | jump | jumpi | pc | jumpdest
  | «return» | revert
  deriving DecidableEq, Repr

def decode (b : UInt8) : Option Op :=
  match b with
  | 0x00 => some .stop
  | 0x01 => some (.binop .add)
  | 0x02 => some (.binop .mul)
  | 0x03 => some (.binop .sub)
  | 0x04 => some (.binop .div)
  | 0x06 => some (.binop .mod)
  | 0x10 => some (.binop .lt)
  | 0x11 => some (.binop .gt)
  | 0x14 => some (.binop .eq)
  | 0x15 => some (.unop .iszero)
  | 0x16 => some (.binop .and)
  | 0x17 => some (.binop .or)
  | 0x18 => some (.binop .xor)
  | 0x19 => some (.unop .not)
  | 0x1b => some (.binop .shl)
  | 0x1c => some (.binop .shr)
  | 0x50 => some .pop
  | 0x51 => some .mload
  | 0x52 => some .mstore
  | 0x53 => some .mstore8
  | 0x54 => some .sload
  | 0x55 => some .sstore
  | 0x56 => some .jump
  | 0x57 => some .jumpi
  | 0x58 => some .pc
  | 0x5b => some .jumpdest
  | 0xf3 => some .return
  | 0xfd => some .revert
  | _ =>
    if 0x5f ≤ b ∧ b ≤ 0x7f then some (.push (b - 0x5f).toNat)
    else if 0x80 ≤ b ∧ b ≤ 0x8f then some (.dup (b - 0x7f).toNat)
    else if 0x90 ≤ b ∧ b ≤ 0x9f then some (.swap (b - 0x8f).toNat)
    else none

/-- An exceptional halt: stack underflow or overflow, an invalid jump, an unsupported opcode,
or memory past `memoryLimit`. -/
def invalid {α : Type} : HostM α := Host.halt .invalid

def pop : List Word → HostM (Word × List Word)
  | a :: rest => pure (a, rest)
  | [] => invalid

/-- Memory accesses must end at or below this byte offset, or the frame halts. Stands in for
running out of gas on memory expansion, and keeps evaluation finite. -/
def memoryLimit : Nat := 2 ^ 32

/-- The offset and length of a memory access, halting past `memoryLimit`. An empty access
touches no memory, whatever its offset. -/
def accessRange (off len : Word) : HostM (Nat × Nat) := do
  if len.toNat = 0 then return (0, 0)
  unless off.toNat + len.toNat ≤ memoryLimit do invalid
  return (off.toNat, len.toNat)

/-- Grows memory with zero bytes to cover `[off, off + len)`, rounded up to whole words. -/
def expand (m : ByteArray) (off len : Nat) : ByteArray :=
  if len = 0 then m else
  let want := (off + len + 31) / 32 * 32
  if m.size < want then m ++ ⟨Array.replicate (want - m.size) 0⟩ else m

/-- The `len` bytes at `off`, and memory expanded to cover them. -/
def memRead (m : ByteArray) (off len : Nat) : ByteArray × ByteArray :=
  let m := expand m off len
  (m.slicePadded off len, m)

def memWrite (m : ByteArray) (off : Nat) (data : ByteArray) : ByteArray :=
  data.copySlice 0 (expand m off data.size) off data.size

/-- Moves to the next instruction with a new stack. -/
def EvmState.advance (s : EvmState) (stack : List Word) : EvmState :=
  { s with pc := s.pc + 1, stack }

def jumpTo (ctx : Context) (s : EvmState) (dst : Word) (stack : List Word) : HostM EvmState := do
  unless ctx.isJumpdest dst do invalid
  return { s with pc := dst.toNat, stack }

/-- Executes `op` at `s.pc`. Returns the state before the next instruction, or halts. -/
def exec (ctx : Context) (s : EvmState) : Op → HostM EvmState
  | .stop => Host.halt (.ret .empty)
  | .unop op => do
    let (a, st) ← pop s.stack
    return s.advance (op.eval a :: st)
  | .binop op => do
    let (a, st) ← pop s.stack
    let (b, st) ← pop st
    return s.advance (op.eval a b :: st)
  | .pop => do
    let (_, st) ← pop s.stack
    return s.advance st
  | .push n =>
    let v := Word.ofBytes (ctx.code.slicePadded (s.pc + 1) n)
    return { s with pc := s.pc + 1 + n, stack := v :: s.stack }
  | .dup n => do
    let some v := s.stack[n - 1]? | invalid
    return s.advance (v :: s.stack)
  | .swap n => do
    let a :: rest := s.stack | invalid
    let some b := rest[n - 1]? | invalid
    return s.advance (b :: rest.set (n - 1) a)
  | .mload => do
    let (off, st) ← pop s.stack
    let (o, l) ← accessRange off 32
    let (data, memory) := memRead s.memory o l
    return { s.advance (Word.ofBytes data :: st) with memory }
  | .mstore => do
    let (off, st) ← pop s.stack
    let (v, st) ← pop st
    let (o, _) ← accessRange off 32
    return { s.advance st with memory := memWrite s.memory o (Word.toBytes { toNat := 32 } v) }
  | .mstore8 => do
    let (off, st) ← pop s.stack
    let (v, st) ← pop st
    let (o, _) ← accessRange off 1
    return { s.advance st with memory := memWrite s.memory o (Word.toBytes { toNat := 1 } v) }
  | .sload => do
    let (k, st) ← pop s.stack
    let v ← Host.persistent.load k
    return s.advance (v :: st)
  | .sstore => do
    let (k, st) ← pop s.stack
    let (v, st) ← pop st
    Host.persistent.store k v
    return s.advance st
  | .jump => do
    let (dst, st) ← pop s.stack
    jumpTo ctx s dst st
  | .jumpi => do
    let (dst, st) ← pop s.stack
    let (cond, st) ← pop st
    if cond = 0 then return s.advance st else jumpTo ctx s dst st
  | .pc => return s.advance (Word.ofNat s.pc :: s.stack)
  | .jumpdest => return s.advance s.stack
  | .return => do
    let (off, st) ← pop s.stack
    let (len, _) ← pop st
    let (o, l) ← accessRange off len
    Host.halt (.ret (memRead s.memory o l).1)
  | .revert => do
    let (off, st) ← pop s.stack
    let (len, _) ← pop st
    let (o, l) ← accessRange off len
    Host.halt (.revert (memRead s.memory o l).1)

/-- One iteration of the interpreter loop. Running off the end of the code is `STOP`. The stack
limit is checked after the instruction: only `PUSHn`, `DUPn` and `PC` grow the stack, and none of
them performs an operation, so this is indistinguishable from checking before. -/
def step (ctx : Context) (s : EvmState) : HostM (IterStep EvmState Empty) := do
  let some b := ctx.code[s.pc]? | Host.halt (.ret .empty)
  let some op := decode b | invalid
  let s' ← exec ctx s op
  unless s'.stack.length ≤ stackLimit do invalid
  return .repeat s'

end Evm
