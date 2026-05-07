import EML.Framework.Builders
import EML.Framework.Builders.Constants
import EML.Framework.Builders.Arithmetic
import EML.Framework.Builders.Transcendental

/-!
# Aggregate import — all EML term builders

Convenience module that pulls in every `Builders/*.lean` so downstream
files (the EL → EML compiler, the closure lemmas) need only one
import line.

| Module | Builders provided |
|---|---|
| `EML.Framework.Builders` | `mkExp`, `mkLog`, `mkSubPos` |
| `EML.Framework.Builders.Constants` | `mkZero`, `mkE`, `mkNegOne`, `mkTwo`, `mkHalf` |
| `EML.Framework.Builders.Arithmetic` | `mkNeg`, `mkAdd`, `mkSub`, `mkMulPos`, `mkInvPos`, `mkSqPos` |
| `EML.Framework.Builders.Transcendental` | `mkSqrtPos`, `mkPowPos`, `mkDivPos`, `mkHalvePos`, `mkAvgPos`, `mkLogbPos`, `mkHypotPos` |

Total: 21 public builders. The Transcendental file privately defines a
local `mkTwo` / `mkHalfClosed` that don't collide because of the
`private` modifier.
-/
