type opComp =
  Eq | Neq | Lt | Le | Gt | Ge


type expType = (* a completer *)
  Id of string
| Cste of int
| Plus of expType*expType
| Times of expType*expType
| Minus of expType*expType
| Div of expType*expType
| Ite of compType*expType*expType
| UMinus of expType

and compType =
  COMP of expType * opComp * expType
| AND of compType * compType
| OR of compType * compType
| NOT of compType

type declType = string * expType

type declListType =
  V of declType * declListType
| N

type progType = declListType * expType

exception VC_Error of string
exception RUN_Error of string
exception MISC_Error of string
