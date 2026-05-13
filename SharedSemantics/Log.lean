import SharedSemantics.Account

namespace SharedSemantics
namespace Log

abbrev Byte := Account.Byte
abbrev Bytes := Account.Bytes

structure Entry where
  address : Word := 0
  topics : List Word := []
  data : Bytes := []
  deriving Repr, DecidableEq

def append (logs : List α) (entry : α) : List α :=
  logs ++ [entry]

def appendEntry (logs : List Entry) (entry : Entry) : List Entry :=
  append logs entry

end Log
end SharedSemantics
