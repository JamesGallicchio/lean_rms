
namespace trellis

mutual inductive typ, exp
with typ : Type
| char : typ
| int : typ
| vec : typ -> exp -> typ
with exp : Type
| 

end trellis
