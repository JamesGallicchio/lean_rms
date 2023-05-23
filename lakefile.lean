import Lake
open System Lake DSL

package «reg-machine»

@[default_target]
lean_lib RegMachine

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

meta if get_config? docs = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
