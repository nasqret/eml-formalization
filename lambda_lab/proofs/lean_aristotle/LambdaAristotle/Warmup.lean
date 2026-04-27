-- Plik używany przez `arist warmup` — ładuje cały Mathlib.Tactic,
-- żeby oleany trafiły do page cache systemu. Dzięki temu następna
-- kompilacja plików z `import Mathlib.Tactic` jest 3-4x szybsza.
import Mathlib.Tactic

namespace LambdaAristotle.Warmup

example : True := trivial

end LambdaAristotle.Warmup
