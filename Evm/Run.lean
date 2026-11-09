import Evm.Step

/-! The EVM interpreter: `step` in a loop from the empty state at `pc = 0`. -/

open Host

namespace Evm

/-- Runs `code` as one frame in `env`. The frame only ends by halting, so it never returns. -/
def run (code : ByteArray) (env : Env) : HostM Empty :=
  CoFree.iter EvmState.initial (step (.ofCode code env))

end Evm
