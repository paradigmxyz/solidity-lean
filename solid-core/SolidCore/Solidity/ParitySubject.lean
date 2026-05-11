import SolidCore.Solidity.ABI

namespace SolidCore
namespace Solidity
namespace Source
namespace ParitySubject

def w (value : Word) : Expr :=
  Expr.word value

def v (name : String) : Expr :=
  Expr.var name

def st (name : String) : Expr :=
  Expr.storage name

def bin (op : BinaryOp) (lhs rhs : Expr) : Expr :=
  Expr.binary op lhs rhs

def add := bin BinaryOp.add
def sub := bin BinaryOp.sub
def mul := bin BinaryOp.mul
def bitAnd := bin BinaryOp.bitAnd
def bitOr := bin BinaryOp.bitOr
def bitXor := bin BinaryOp.bitXor
def shl := bin BinaryOp.shl
def shr := bin BinaryOp.shr
def lt := bin BinaryOp.lt
def gt := bin BinaryOp.gt
def eq := bin BinaryOp.eq

def len (expr : Expr) : Expr :=
  Expr.length expr

def idx (base index : Expr) : Expr :=
  Expr.index base index

def assignVar (name : String) (expr : Expr) : Stmt :=
  Stmt.assign (LValue.var name) expr

def assignStorage (name : String) (expr : Expr) : Stmt :=
  Stmt.assign (LValue.storage name) expr

def assignIndex (name : String) (index expr : Expr) : Stmt :=
  Stmt.assign (LValue.index (LValue.var name) index) expr

def assignOpVar (name : String) (op : BinaryOp) (expr : Expr) : Stmt :=
  Stmt.assignOp (LValue.var name) op expr

def addAssign (name : String) (expr : Expr) : Stmt :=
  assignOpVar name BinaryOp.add expr

def subAssign (name : String) (expr : Expr) : Stmt :=
  assignOpVar name BinaryOp.sub expr

def xorAssign (name : String) (expr : Expr) : Stmt :=
  assignOpVar name BinaryOp.bitXor expr

def incVar (name : String) : Stmt :=
  addAssign name (w 1)

def uintDecl (name : String) (expr : Expr) : Stmt :=
  Stmt.varDecl Ty.uint256 name (some expr)

def pureLoopBody : Stmt :=
  Stmt.block
    [ uintDecl "acc" (add (v "x") (w 3))
    , Stmt.forLoop
        (uintDecl "i" (w 0))
        (lt (v "i") (v "rounds"))
        (incVar "i")
        (Stmt.block
          [ Stmt.ifElse
              (eq (bitAnd (v "i") (w 1)) (w 0))
              (assignVar "acc"
                (bitXor
                  (add (mul (v "acc") (w 3)) (v "i"))
                  (shr (v "acc") (w 1))))
              (assignVar "acc"
                (bitXor
                  (add (v "acc") (mul (v "i") (w 7)))
                  (shl (v "acc") (w 2))))
          , Stmt.ifElse
              (eq (bitAnd (v "acc") (w 0xff)) (w 0x42))
              (addAssign "acc" (w 0x99))
              (Stmt.ifElse
                (eq (bitAnd (v "acc") (w 0x0f)) (w 0x0a))
                (xorAssign "acc" (w 0x1234))
                (addAssign "acc" (sub (v "rounds") (v "i"))))
          ])
    , uintDecl "j" (v "rounds")
    , Stmt.whileLoop
        (gt (v "j") (w 0))
        (Stmt.block
          [ assignVar "acc"
              (add (bitXor (v "acc") (v "j"))
                (shl (v "j") (w 3)))
          , Stmt.unchecked (subAssign "j" (w 1))
          ])
    , Stmt.returnValues [v "acc"]
    ]

def memoryCrunchBody : Stmt :=
  Stmt.block
    [ Stmt.varDecl (fixedWordArray 8) "ring" none
    , assignIndex "ring" (w 0) (v "a")
    , assignIndex "ring" (w 1) (v "b")
    , assignVar "sum" (add (v "a") (v "b"))
    , Stmt.forLoop
        (uintDecl "i" (w 2))
        (lt (v "i") (add (v "rounds") (w 2)))
        (incVar "i")
        (Stmt.block
          [ uintDecl "left"
              (idx (v "ring") (bitAnd (sub (v "i") (w 1)) (w 7)))
          , uintDecl "right"
              (idx (v "ring") (bitAnd (sub (v "i") (w 2)) (w 7)))
          , uintDecl "next"
              (add (add (v "left") (v "right"))
                (mul (v "i") (w 11)))
          , assignIndex "ring" (bitAnd (v "i") (w 7)) (v "next")
          , addAssign "sum" (v "next")
          , xorAssign "folded"
              (bitOr
                (shl (v "next") (bitAnd (v "i") (w 7)))
                (shr (v "next")
                  (bitAnd (add (v "i") (w 1)) (w 7))))
          ])
    , assignVar "last"
        (idx (v "ring") (bitAnd (add (v "rounds") (w 1)) (w 7)))
    ]

def bytesLoopBody : Stmt :=
  Stmt.block
    [ assignVar "acc" (bitXor (v "salt") (len (v "data")))
    , Stmt.forLoop
        (uintDecl "i" (w 0))
        (lt (v "i") (len (v "data")))
        (incVar "i")
        (Stmt.block
          [ uintDecl "value" (idx (v "data") (v "i"))
          , Stmt.ifElse
              (eq (bitAnd (v "value") (w 1)) (w 0))
              (addAssign "acc" (mul (v "value") (add (v "i") (w 1))))
              (xorAssign "acc"
                (shl (v "value") (bitAnd (v "i") (w 15))))
          , assignVar "acc"
              (bitXor
                (bitXor (shl (v "acc") (w 1)) (shr (v "acc") (w 3)))
                (w 0x55))
          ])
    ]

def storageMixBody : Stmt :=
  Stmt.block
    [ uintDecl "local" (st "total")
    , uintDecl "localSeed" (st "seed")
    , Stmt.forLoop
        (uintDecl "i" (w 0))
        (lt (v "i") (v "rounds"))
        (incVar "i")
        (Stmt.block
          [ addAssign "local" (add (v "inc") (v "i"))
          , Stmt.ifElse
              (eq (bitAnd (v "local") (w 1)) (w 0))
              (xorAssign "localSeed"
                (add (v "local") (shl (v "i") (w 4))))
              (addAssign "localSeed"
                (bitAnd (bitXor (v "local") (v "i")) (w 0xffff)))
          ])
    , assignStorage "flag" (add (bitAnd (v "localSeed") (w 1)) (v "rounds"))
    , assignStorage "total" (v "local")
    , assignStorage "seed" (v "localSeed")
    , Stmt.emitEvent "Mixed"
        [v "rounds", st "flag", v "local", v "localSeed"]
    , Stmt.returnValues [bitXor (bitXor (v "local") (v "localSeed")) (st "flag")]
    ]

def guardedBody : Stmt :=
  Stmt.block
    [ Stmt.ifElse
        (lt (v "value") (v "minimum"))
        (Stmt.revert "TooSmall" [v "value", v "minimum"])
        Stmt.skip
    , Stmt.returnValues
        [add (mul (sub (v "value") (v "minimum")) (w 17)) (w 1)]
    ]

def pureLoop : FunctionDef :=
  { name := "pureLoop"
    selector? := some 0x474e9c3c
    params := [uint256 "rounds", uint256 "x"]
    returns := [uint256 "$ret0"]
    body := pureLoopBody }

def memoryCrunch : FunctionDef :=
  { name := "memoryCrunch"
    selector? := some 0xa523070d
    params := [uint256 "a", uint256 "b", uint256 "rounds"]
    returns := [uint256 "sum", uint256 "folded", uint256 "last"]
    body := memoryCrunchBody }

def bytesLoop : FunctionDef :=
  { name := "bytesLoop"
    selector? := some 0x8d91096c
    params := [bytesCalldata "data", uint256 "salt"]
    returns := [uint256 "acc"]
    body := bytesLoopBody }

def storageMix : FunctionDef :=
  { name := "storageMix"
    selector? := some 0xe67af7d9
    params := [uint256 "rounds", uint256 "inc"]
    returns := [uint256 "out"]
    body := storageMixBody }

def guarded : FunctionDef :=
  { name := "guarded"
    selector? := some 0x252fc58f
    params := [uint256 "value", uint256 "minimum"]
    returns := [uint256 "$ret0"]
    body := guardedBody }

def contract : Contract :=
  { storageFields :=
      [ { name := "total", slot := 0 }
      , { name := "seed", slot := 1 }
      , { name := "flag", slot := 2 }
      ]
    eventDecls := [{ name := "Mixed", indexedCount := 2 }]
    errorDecls :=
      [{ name := "TooSmall"
         selector := 0xe94fe3af
         fields := [Ty.uint256, Ty.uint256] }]
    functions := [pureLoop, memoryCrunch, bytesLoop, storageMix, guarded] }

def bytesLoopInput : List Byte :=
  [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
   0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff]

def storageMixInitialState : State :=
  (((State.empty.storeSlot 0 3).storeSlot 1 11).storeSlot 2 0)

def callByName (fuel : Nat) (name : String)
    (state : State) (args : List Value) : Option CallResult :=
  contract.call? fuel (CallTarget.name name) state args

def pureLoopResult : Option CallResult :=
  callByName 1000 "pureLoop" State.empty [Value.word 19, Value.word 7]

def memoryCrunchResult : Option CallResult :=
  callByName 1000 "memoryCrunch" State.empty
    [Value.word 9, Value.word 13, Value.word 12]

def bytesLoopResult : Option CallResult :=
  callByName 1000 "bytesLoop" State.empty
    [Value.bytes bytesLoopInput, Value.word 0x1234]

def storageMixResult : Option CallResult :=
  callByName 1000 "storageMix" storageMixInitialState
    [Value.word 8, Value.word 5]

def guardedRevertResult : Option CallResult :=
  callByName 100 "guarded" State.empty [Value.word 5, Value.word 9]

def calldataFor? (function : FunctionDef) (args : List Value) :
    Option ABI.Bytes :=
  ABI.calldataFor? function args

def callCalldata? (fuel : Nat) (state : State) (calldata : ABI.Bytes) :
    Option ABI.AbiCallResult :=
  ABI.Contract.callCalldata? fuel contract state calldata

def pureLoopCalldata? : Option ABI.Bytes :=
  calldataFor? pureLoop [Value.word 19, Value.word 7]

def memoryCrunchCalldata? : Option ABI.Bytes :=
  calldataFor? memoryCrunch [Value.word 9, Value.word 13, Value.word 12]

def bytesLoopCalldata? : Option ABI.Bytes :=
  calldataFor? bytesLoop [Value.bytes bytesLoopInput, Value.word 0x1234]

def storageMixCalldata? : Option ABI.Bytes :=
  calldataFor? storageMix [Value.word 8, Value.word 5]

def guardedCalldata? : Option ABI.Bytes :=
  calldataFor? guarded [Value.word 5, Value.word 9]

def pureLoopAbiResult? : Option ABI.AbiCallResult :=
  pureLoopCalldata?.bind (callCalldata? 1000 State.empty)

def memoryCrunchAbiResult? : Option ABI.AbiCallResult :=
  memoryCrunchCalldata?.bind (callCalldata? 1000 State.empty)

def bytesLoopAbiResult? : Option ABI.AbiCallResult :=
  bytesLoopCalldata?.bind (callCalldata? 1000 State.empty)

def storageMixAbiResult? : Option ABI.AbiCallResult :=
  storageMixCalldata?.bind (callCalldata? 1000 storageMixInitialState)

def guardedAbiResult? : Option ABI.AbiCallResult :=
  guardedCalldata?.bind (callCalldata? 100 State.empty)

end ParitySubject
end Source
end Solidity
end SolidCore
