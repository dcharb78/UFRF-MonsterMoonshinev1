import Lake
open Lake DSL

package «MonsterMoonshineUFRF» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0-rc2"

lean_lib «MonsterMoonshineUFRF» where
  roots := #[`Monster_Moonshine, `PhaseLog_Monoid, `Concurrency_BoundedGap]
