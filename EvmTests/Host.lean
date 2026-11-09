import Evm
import ITree.Run

/-! A test host for `Evm.run`: storage is a map threaded through the run, `halt` ends it, and
every other host operation is reported as unsupported (no test program uses one). -/

open Host

namespace EvmTests

inductive Result
  | ret (data : List UInt8)
  | revert (data : List UInt8)
  | invalid
  | selfdestruct (beneficiary : Address)
  | unsupported
  | outOfFuel
  deriving DecidableEq, Repr

/-- Why a run stopped before returning (an `Evm.run` never returns). -/
inductive Stop
  | halt (outcome : SimplifiedOutcome)
  | unsupported

/-- Errors are inside the state, so the storage survives a halt. -/
abbrev TestM := ExceptT Stop (StateM Storage)

def answer : (op : HostE.Op) → TestM (HostE.Resp op)
  | .sload k => return (← get) k
  | .sstore k v => modify (·.set k v)
  | .halt o => throw (.halt o)
  | _ => throw .unsupported

def pick : (c : NonDeterminism.none.Op) → TestM (NonDeterminism.none.Resp c) := nofun

def testEnv : Env where
  address := 0xA0
  origin := 0xC0
  caller := 0xC0
  callvalue := 0
  gasprice := 1
  chainid := 1
  coinbase := 0
  timestamp := 1
  number := 1
  prevrandao := 0
  gaslimit := 30000000
  basefee := 1
  blobbasefee := 1
  blockhash _ := 0
  blobhash _ := 0

structure Run where
  result : Result
  storage : Storage

def ofStop : Stop → Result
  | .halt (.ret d) => .ret d.toList
  | .halt (.revert d) => .revert d.toList
  | .halt .invalid => .invalid
  | .halt (.selfdestruct a) => .selfdestruct a
  | .unsupported => .unsupported

/-- Runs `code` with `storage` for at most `fuel` steps of the tree. -/
def run (code : List UInt8) (storage : Storage := fun _ => 0) (fuel : Nat := 100000) : Run :=
  let (r, st) := ((CoFree.runM answer pick fuel (Evm.run ⟨code.toArray⟩ testEnv)).run).run storage
  match r with
  | .ok none => ⟨.outOfFuel, st⟩
  | .ok (some e) => nomatch e
  | .error s => ⟨ofStop s, st⟩

/-- The run returned exactly the 32-byte word `w`. -/
def Run.returnsWord (r : Run) (w : Word) : Bool :=
  r.result == .ret (Word.toBytes { toNat := 32 } w).toList

end EvmTests
