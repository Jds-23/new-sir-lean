import Host.Effect

/-! The EVM interpreter's state and its fixed context.

The stack, memory and program counter are plain interpreter state: the EVM has no internal
call stack, so nothing needs a separate effect layer. Storage and everything else outside the
frame is reached through `HostE`. -/

open Host

namespace Evm

/-- The maximum stack depth. -/
def stackLimit : Nat := 1024

/-- The running frame's mutable state. The head of `stack` is the top of the EVM stack. -/
structure EvmState where
  pc : Nat
  stack : List Word
  memory : ByteArray

def EvmState.initial : EvmState := ⟨0, [], .empty⟩

/-- The number of immediate bytes following `op`: `n` for `PUSHn` (`0x60`–`0x7f`), else `0`. -/
def immediateSize (op : UInt8) : Nat :=
  if 0x60 ≤ op ∧ op ≤ 0x7f then (op - 0x5f).toNat else 0

/-- `true` at every offset holding a `JUMPDEST` (`0x5b`) that is an instruction, not part of a
`PUSHn` immediate. -/
def jumpdests (code : ByteArray) : Array Bool :=
  go 0 (Array.replicate code.size false)
where
  go (pc : Nat) (acc : Array Bool) : Array Bool :=
    if h : pc < code.size then
      let op := code[pc]
      go (pc + 1 + immediateSize op) (if op = 0x5b then acc.setIfInBounds pc true else acc)
    else acc
  termination_by code.size - pc

/-- What stays fixed while a frame runs: its code, its environment, and the code's valid jump
destinations. -/
structure Context where
  code : ByteArray
  env : Env
  jumpdests : Array Bool

def Context.ofCode (code : ByteArray) (env : Env) : Context := ⟨code, env, Evm.jumpdests code⟩

def Context.isJumpdest (ctx : Context) (dst : Word) : Bool := ctx.jumpdests.getD dst.toNat false

end Evm
