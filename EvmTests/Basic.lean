import EvmTests.Host

/-! Hand-assembled programs run through `Evm.run` and checked at build time. -/

namespace EvmTests

/-! ## Opcode bytes -/

def STOP : UInt8 := 0x00
def ADD : UInt8 := 0x01
def MUL : UInt8 := 0x02
def SUB : UInt8 := 0x03
def DIV : UInt8 := 0x04
def MOD : UInt8 := 0x06
def LT : UInt8 := 0x10
def GT : UInt8 := 0x11
def EQ : UInt8 := 0x14
def ISZERO : UInt8 := 0x15
def AND : UInt8 := 0x16
def OR : UInt8 := 0x17
def XOR : UInt8 := 0x18
def NOT : UInt8 := 0x19
def SHL : UInt8 := 0x1b
def SHR : UInt8 := 0x1c
def POP : UInt8 := 0x50
def MLOAD : UInt8 := 0x51
def MSTORE : UInt8 := 0x52
def MSTORE8 : UInt8 := 0x53
def SLOAD : UInt8 := 0x54
def SSTORE : UInt8 := 0x55
def JUMP : UInt8 := 0x56
def JUMPI : UInt8 := 0x57
def PC : UInt8 := 0x58
def JUMPDEST : UInt8 := 0x5b
def PUSH0 : UInt8 := 0x5f
def PUSH1 : UInt8 := 0x60
def PUSH2 : UInt8 := 0x61
def PUSH32 : UInt8 := 0x7f
def DUP1 : UInt8 := 0x80
def DUP2 : UInt8 := 0x81
def SWAP1 : UInt8 := 0x90
def SWAP2 : UInt8 := 0x91
def RETURN : UInt8 := 0xf3
def REVERT : UInt8 := 0xfd

/-- Stores the top of the stack at memory 0 and returns those 32 bytes. -/
def ret32 : List UInt8 := [PUSH1, 0, MSTORE, PUSH1, 32, PUSH1, 0, RETURN]

/-! ## Arithmetic: `SUB a b` is `a - b` with `a` on top -/

#guard (run ([PUSH1, 3, PUSH1, 4, ADD, PUSH1, 5, MUL] ++ ret32)).returnsWord 35
#guard (run ([PUSH1, 3, PUSH1, 10, SUB] ++ ret32)).returnsWord 7
#guard (run ([PUSH1, 10, PUSH1, 3, SUB] ++ ret32)).returnsWord (0 - 7)
#guard (run ([PUSH1, 0, PUSH1, 7, DIV] ++ ret32)).returnsWord 0
#guard (run ([PUSH1, 3, PUSH1, 10, MOD] ++ ret32)).returnsWord 1

/-! ## Comparison and bitwise -/

-- `2 < 1` is 0, `ISZERO` makes it 1, shifted left by 4.
#guard (run ([PUSH1, 1, PUSH1, 2, LT, ISZERO, PUSH1, 4, SHL] ++ ret32)).returnsWord 16
#guard (run ([PUSH1, 1, PUSH1, 2, GT, PUSH1, 5, PUSH1, 5, EQ, ADD] ++ ret32)).returnsWord 2
#guard (run ([PUSH1, 0x0c, PUSH1, 0x0a, AND, PUSH1, 0x01, OR, PUSH1, 0xff, XOR] ++ ret32)).returnsWord 0xf6
#guard (run ([PUSH0, NOT, PUSH1, 255, SHR] ++ ret32)).returnsWord 1

/-! ## Stack: `DUPn`, `SWAPn`, `POP`, `PC`, truncated `PUSH` -/

-- Stack `[1, 2, 3]` (top first); `SWAP2` gives `[3, 2, 1]`; `DUP2` pushes 2; `SUB` is 2 - 3.
#guard (run ([PUSH1, 3, PUSH1, 2, PUSH1, 1, SWAP2, DUP2, SUB] ++ ret32)).returnsWord (0 - 1)
#guard (run ([PUSH1, 9, PUSH1, 8, POP, DUP1, ADD] ++ ret32)).returnsWord 18
#guard (run ([PUSH0, POP, PC] ++ ret32)).returnsWord 2
-- `PUSH2` with one byte left reads it as the high byte, zero-padded.
#guard (run [PUSH2, 0x01]).result == .ret []

/-! ## Control flow -/

/-- Counts to `n` in a `JUMPI` loop, then stores the count in slot 0.
```
0:  PUSH1 0
2:  JUMPDEST            ; i
3:  PUSH1 1 ADD         ; i + 1
6:  DUP1 PUSH1 n EQ     ; i = n, i
10: ISZERO PUSH1 2 JUMPI
14: PUSH1 0 SSTORE STOP
``` -/
def countTo (n : UInt8) : List UInt8 :=
  [PUSH1, 0, JUMPDEST, PUSH1, 1, ADD, DUP1, PUSH1, n, EQ, ISZERO, PUSH1, 2, JUMPI,
    PUSH1, 0, SSTORE, STOP]

#guard let r := run (countTo 10); r.result == .ret [] && r.storage 0 == 10
#guard let r := run (countTo 200); r.result == .ret [] && r.storage 0 == 200

-- `JUMPI` with a zero condition falls through.
#guard (run ([PUSH1, 7, PUSH0, PUSH1, 0, JUMPI] ++ ret32)).returnsWord 7

-- Byte 4 is `0x5b`, but it is the immediate of the `PUSH1` at 3, so not a `JUMPDEST`.
#guard (run [PUSH1, 4, JUMP, PUSH1, JUMPDEST, STOP]).result == .invalid
-- The same jump to a real `JUMPDEST` succeeds.
#guard (run [PUSH1, 4, JUMP, STOP, JUMPDEST, PUSH1, 1, PUSH0, RETURN]).result == .ret [0]
-- A jump to an ordinary instruction.
#guard (run [PUSH1, 3, JUMP, STOP]).result == .invalid

/-! ## Memory -/

def word32 : List UInt8 := (List.range 32).map fun i => (i + 1).toUInt8

-- An unaligned `MSTORE`/`MLOAD` round trip.
#guard (run ([PUSH32] ++ word32 ++ [PUSH1, 5, MSTORE, PUSH1, 5, MLOAD] ++ ret32)).returnsWord
  (Word.ofBytes ⟨word32.toArray⟩)
-- `MSTORE8` stores the low byte; `RETURN` past written memory reads zeros.
#guard (run [PUSH2, 0x12, 0x34, PUSH1, 1, MSTORE8, PUSH1, 3, PUSH0, RETURN]).result ==
  .ret [0, 0x34, 0]
-- `MLOAD` of untouched memory is zero.
#guard (run ([PUSH1, 0x40, MLOAD] ++ ret32)).returnsWord 0
-- Memory past the limit halts instead of allocating.
#guard (run [PUSH1, 1, PUSH32, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, MSTORE8]).result == .invalid

/-! ## Storage -/

#guard let r := run ([PUSH1, 42, PUSH1, 7, SSTORE, PUSH1, 7, SLOAD] ++ ret32)
  r.returnsWord 42 && r.storage 7 == 42 && r.storage 0 == 0
-- Reads the initial storage.
#guard (run ([PUSH1, 3, SLOAD] ++ ret32) (storage := fun k => k * 2)).returnsWord 6

/-! ## Halting -/

#guard (run [PUSH2, 0xbe, 0xef, PUSH0, MSTORE, PUSH1, 2, PUSH1, 30, REVERT]).result ==
  .revert [0xbe, 0xef]
#guard (run [PUSH1, 1, PUSH1, 2, STOP, ADD]).result == .ret []
-- Running off the end of the code is `STOP`.
#guard (run [PUSH1, 1]).result == .ret []
#guard (run []).result == .ret []
-- Stack underflow.
#guard (run [PUSH1, 1, ADD]).result == .invalid
#guard (run [PUSH1, 1, SWAP1]).result == .invalid
-- Unsupported opcode (`INVALID`, and `BALANCE` outside the subset).
#guard (run [0xfe]).result == .invalid
#guard (run [PUSH0, 0x31]).result == .invalid
-- Stack overflow: each iteration leaves one more word, the 1025th halts.
#guard (run [JUMPDEST, PUSH0, PUSH0, JUMP]).result == .invalid
-- Fuel runs out on an infinite loop that keeps the stack flat.
#guard (run [JUMPDEST, PUSH0, JUMP] (fuel := 1000)).result == .outOfFuel

/-! ## Kernel-checked

The same evaluation, as proofs the kernel checks by reduction: `Evm.run` reduces in the kernel,
so facts about concrete programs need no compiled evaluation. -/

example : (run ([PUSH1, 3, PUSH1, 4, ADD, PUSH1, 5, MUL] ++ ret32)).returnsWord 35 = true := by
  decide +kernel
example : (run [PUSH1, 4, JUMP, PUSH1, JUMPDEST, STOP]).result = .invalid := by decide +kernel
example : (run [PUSH1, 1, ADD]).result = .invalid := by decide +kernel
example : (run ([PUSH1, 42, PUSH1, 7, SSTORE, PUSH1, 7, SLOAD] ++ ret32)).returnsWord 42 = true := by
  decide +kernel
example : (run (countTo 5)).storage 0 = 5 := by decide +kernel

end EvmTests
