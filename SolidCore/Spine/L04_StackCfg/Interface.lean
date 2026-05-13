import SharedSemantics.Word
import SolidCore.Spine.L03_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace L04_StackCfg

abbrev Word := SharedSemantics.Word
abbrev Byte := Nat

structure Label where
  value : Nat
  deriving Repr, DecidableEq

structure FunctionId where
  value : Nat
  deriving Repr, DecidableEq

inductive Atom where
  | word : Word -> Atom
  | label : Label -> Atom
  | function : FunctionId -> Atom
  deriving Repr, DecidableEq

inductive PrimOp where
  | add
  | mul
  | sub
  | div
  | sdiv
  | modOp
  | smod
  | addmod
  | mulmod
  | exp
  | signextend
  | lt
  | gt
  | slt
  | sgt
  | eq
  | iszero
  | andOp
  | orOp
  | xor
  | notOp
  | byteOp
  | shl
  | shr
  | sar
  | keccak256
  | mload
  | mstore
  | mstore8
  | sload
  | sstore
  | calldataload
  | calldatacopy
  | returndatacopy
  | codecopy
  | extcodecopy
  | log : Nat -> PrimOp
  | create
  | create2
  | call
  | callcode
  | delegatecall
  | staticcall
  | selfdestruct
  deriving Repr, DecidableEq

inductive EnvOp where
  | address
  | balance
  | origin
  | caller
  | callvalue
  | calldatasize
  | codesize
  | gasprice
  | extcodesize
  | returndatasize
  | extcodehash
  | blockhash
  | coinbase
  | timestamp
  | number
  | prevrandao
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | blobhash
  | blobbasefee
  | pc
  | msize
  | gas
  deriving Repr, DecidableEq

structure Shuffle where
  inputs : Nat
  outputs : List Nat := []
  deriving Repr, DecidableEq

inductive PseudoInstr where
  | shuffle : Shuffle -> PseudoInstr
  | dropMany : Nat -> PseudoInstr
  | copyTop : Nat -> PseudoInstr
  | materializeDataOffset : L03_GeneratedYul.DataLabel -> PseudoInstr
  | materializeDataSize : L03_GeneratedYul.DataLabel -> PseudoInstr
  deriving Repr, DecidableEq

inductive Instr where
  | push : Atom -> Instr
  | dup : Nat -> Instr
  | swap : Nat -> Instr
  | pop : Instr
  | op : PrimOp -> Instr
  | env : EnvOp -> Instr
  | pseudo : PseudoInstr -> Instr
  deriving Repr, DecidableEq

def Instr.PseudoFree : Instr -> Prop
  | Instr.pseudo _ => False
  | _ => True

def InstrsPseudoFree (code : List Instr) : Prop :=
  ∀ instr, instr ∈ code -> instr.PseudoFree

def Instr.stackDepthAfter? : Nat -> Instr -> Option Nat
  | depth, Instr.push _ => some (depth + 1)
  | depth, Instr.dup index =>
      if index < depth then some (depth + 1) else none
  | depth, Instr.swap index =>
      if index + 1 < depth then some depth else none
  | depth + 1, Instr.pop => some depth
  | 0, Instr.pop => none
  | 0, Instr.op PrimOp.add => none
  | 1, Instr.op PrimOp.add => none
  | depth + 2, Instr.op PrimOp.add => some (depth + 1)
  | 0, Instr.op PrimOp.mul => none
  | 1, Instr.op PrimOp.mul => none
  | depth + 2, Instr.op PrimOp.mul => some (depth + 1)
  | 0, Instr.op PrimOp.div => none
  | 1, Instr.op PrimOp.div => none
  | depth + 2, Instr.op PrimOp.div => some (depth + 1)
  | 0, Instr.op PrimOp.signextend => none
  | 1, Instr.op PrimOp.signextend => none
  | depth + 2, Instr.op PrimOp.signextend => some (depth + 1)
  | 0, Instr.op PrimOp.modOp => none
  | 1, Instr.op PrimOp.modOp => none
  | depth + 2, Instr.op PrimOp.modOp => some (depth + 1)
  | 0, Instr.op PrimOp.sub => none
  | 1, Instr.op PrimOp.sub => none
  | depth + 2, Instr.op PrimOp.sub => some (depth + 1)
  | 0, Instr.op PrimOp.eq => none
  | 1, Instr.op PrimOp.eq => none
  | depth + 2, Instr.op PrimOp.eq => some (depth + 1)
  | 0, Instr.op PrimOp.lt => none
  | 1, Instr.op PrimOp.lt => none
  | depth + 2, Instr.op PrimOp.lt => some (depth + 1)
  | 0, Instr.op PrimOp.gt => none
  | 1, Instr.op PrimOp.gt => none
  | depth + 2, Instr.op PrimOp.gt => some (depth + 1)
  | 0, Instr.op PrimOp.andOp => none
  | 1, Instr.op PrimOp.andOp => none
  | depth + 2, Instr.op PrimOp.andOp => some (depth + 1)
  | 0, Instr.op PrimOp.orOp => none
  | 1, Instr.op PrimOp.orOp => none
  | depth + 2, Instr.op PrimOp.orOp => some (depth + 1)
  | 0, Instr.op PrimOp.xor => none
  | 1, Instr.op PrimOp.xor => none
  | depth + 2, Instr.op PrimOp.xor => some (depth + 1)
  | 0, Instr.op PrimOp.byteOp => none
  | 1, Instr.op PrimOp.byteOp => none
  | depth + 2, Instr.op PrimOp.byteOp => some (depth + 1)
  | 0, Instr.op PrimOp.shl => none
  | 1, Instr.op PrimOp.shl => none
  | depth + 2, Instr.op PrimOp.shl => some (depth + 1)
  | 0, Instr.op PrimOp.shr => none
  | 1, Instr.op PrimOp.shr => none
  | depth + 2, Instr.op PrimOp.shr => some (depth + 1)
  | 0, Instr.op PrimOp.sar => none
  | 1, Instr.op PrimOp.sar => none
  | depth + 2, Instr.op PrimOp.sar => some (depth + 1)
  | 0, Instr.op PrimOp.iszero => none
  | depth + 1, Instr.op PrimOp.iszero => some (depth + 1)
  | 0, Instr.op PrimOp.notOp => none
  | depth + 1, Instr.op PrimOp.notOp => some (depth + 1)
  | _, _ => none

def stackDepthAfter? : Nat -> List Instr -> Option Nat
  | depth, [] => some depth
  | depth, instr :: rest => do
      let depth' ← Instr.stackDepthAfter? depth instr
      stackDepthAfter? depth' rest

inductive Term where
  | jump : Label -> Term
  | jumpi : Label -> Label -> Term
  | switch : List (Word × Label) -> Label -> Term
  | call : FunctionId -> Nat -> Nat -> Label -> Term
  | returnOp
  | revert
  | stop
  | invalid
  deriving Repr, DecidableEq

structure StackSignature where
  inputDepth : Nat
  outputDepth : Option Nat := none
  maxExtraDepth : Nat := 0
  deriving Repr, DecidableEq

structure Block where
  label : Label
  signature : StackSignature
  body : List Instr := []
  term : Term
  deriving Repr, DecidableEq

structure Function where
  id : FunctionId
  entry : Label
  params : Nat := 0
  returns : Nat := 0
  blocks : List Block := []
  deriving Repr, DecidableEq

structure Program where
  entry : Label
  blocks : List Block := []
  functions : List Function := []
  deriving Repr, DecidableEq

def Term.targets : Term -> List Label
  | Term.jump label => [label]
  | Term.jumpi thenLabel elseLabel => [thenLabel, elseLabel]
  | Term.switch cases default => default :: cases.map (fun c => c.snd)
  | Term.call _ _ _ returnLabel => [returnLabel]
  | Term.returnOp => []
  | Term.revert => []
  | Term.stop => []
  | Term.invalid => []

def Term.calledFunctionIds : Term -> List FunctionId
  | Term.call functionId _ _ _ => [functionId]
  | _ => []

def Program.blockLabels (program : Program) : List Label :=
  program.blocks.map (fun block => block.label)

def Program.functionIds (program : Program) : List FunctionId :=
  program.functions.map (fun function => function.id)

def Function.allBlocks (function : Function) : List Block :=
  function.blocks

def Program.functionBlocks (program : Program) : List Block :=
  program.functions.flatMap Function.allBlocks

def Program.allBlocks (program : Program) : List Block :=
  program.blocks ++ program.functionBlocks

def Program.allBlockLabels (program : Program) : List Label :=
  program.allBlocks.map (fun block => block.label)

def lookupBlock? : List Block -> Label -> Option Block
  | [], _ => none
  | block :: rest, label =>
      if block.label.value = label.value then
        some block
      else
        lookupBlock? rest label

def lookupFunction? : List Function -> FunctionId -> Option Function
  | [], _ => none
  | function :: rest, functionId =>
      if function.id.value = functionId.value then
        some function
      else
        lookupFunction? rest functionId

def Program.LabelsClosed (program : Program) : Prop :=
  program.entry ∈ program.allBlockLabels ∧
    (∀ function, function ∈ program.functions ->
      function.entry ∈ program.allBlockLabels) ∧
    ∀ block, block ∈ program.allBlocks ->
      ∀ target, target ∈ block.term.targets ->
        target ∈ program.allBlockLabels

def Program.LabelsUnique (program : Program) : Prop :=
  program.allBlockLabels.Nodup

def Program.FunctionIdsUnique (program : Program) : Prop :=
  program.functionIds.Nodup

def Program.FunctionCallsClosed (program : Program) : Prop :=
  ∀ block, block ∈ program.allBlocks ->
    ∀ functionId, functionId ∈ block.term.calledFunctionIds ->
      functionId ∈ program.functionIds

def Program.BlocksPseudoFree (program : Program) : Prop :=
  ∀ block, block ∈ program.allBlocks -> InstrsPseudoFree block.body

def Program.labelInputDepth? (program : Program) (label : Label) :
    Option Nat :=
  match lookupBlock? program.allBlocks label with
  | some block => some block.signature.inputDepth
  | none => none

def Program.functionSignature? (program : Program)
    (functionId : FunctionId) : Option (Nat × Nat) :=
  match lookupFunction? program.functions functionId with
  | some function => some (function.params, function.returns)
  | none => none

def Term.StackInputChecked : Term -> Nat -> Prop
  | Term.jumpi _ _, depth => 1 <= depth
  | Term.switch _ _, depth => 1 <= depth
  | Term.call _ params _ _, depth => params <= depth
  | Term.returnOp, depth => 1 <= depth
  | _, _ => True

theorem Term.jumpi_stackInputChecked_iff
    (thenLabel elseLabel : Label) (depth : Nat) :
    (Term.jumpi thenLabel elseLabel).StackInputChecked depth ↔
      1 <= depth := by
  rfl

theorem Term.switch_stackInputChecked_iff
    (cases : List (Word × Label)) (default : Label) (depth : Nat) :
    (Term.switch cases default).StackInputChecked depth ↔ 1 <= depth := by
  rfl

theorem Term.call_stackInputChecked_iff
    (functionId : FunctionId) (params returns : Nat)
    (returnLabel : Label) (depth : Nat) :
    (Term.call functionId params returns returnLabel).StackInputChecked depth ↔
      params <= depth := by
  rfl

theorem Term.return_stackInputChecked_iff (depth : Nat) :
    Term.returnOp.StackInputChecked depth ↔ 1 <= depth := by
  rfl

def Term.SuccessorStackSignaturesChecked
    (program : Program) (depth : Nat) : Term -> Prop
  | Term.jump label =>
      program.labelInputDepth? label = some depth
  | Term.jumpi thenLabel elseLabel =>
      match depth with
      | 0 => False
      | depth' + 1 =>
          program.labelInputDepth? thenLabel = some depth' ∧
            program.labelInputDepth? elseLabel = some depth'
  | Term.switch cases default =>
      match depth with
      | 0 => False
      | depth' + 1 =>
          program.labelInputDepth? default = some depth' ∧
            ∀ branch, branch ∈ cases ->
              program.labelInputDepth? branch.snd = some depth'
  | Term.call functionId params returns returnLabel =>
      params <= depth ∧
        program.functionSignature? functionId = some (params, returns) ∧
        program.labelInputDepth? returnLabel =
          some (depth - params + returns)
  | Term.returnOp => True
  | Term.revert => True
  | Term.stop => True
  | Term.invalid => True

def Block.StackSignatureChecked (block : Block) : Prop :=
  match stackDepthAfter? block.signature.inputDepth block.body,
      block.signature.outputDepth with
  | some actual, some expected =>
      actual = expected ∧ block.term.StackInputChecked actual
  | some actual, none => block.term.StackInputChecked actual
  | none, _ => False

def Program.StackSignaturesChecked (program : Program) : Prop :=
  ∀ block, block ∈ program.allBlocks -> block.StackSignatureChecked

def Function.EntrySignatureChecked (program : Program)
    (function : Function) : Prop :=
  program.labelInputDepth? function.entry = some function.params

def Program.FunctionEntrySignaturesChecked (program : Program) : Prop :=
  ∀ function, function ∈ program.functions ->
    Function.EntrySignatureChecked program function

def Block.SuccessorStackSignaturesChecked
    (program : Program) (block : Block) : Prop :=
  match stackDepthAfter? block.signature.inputDepth block.body with
  | some actual =>
      Term.SuccessorStackSignaturesChecked program actual block.term
  | none => False

def Program.SuccessorStackSignaturesChecked (program : Program) : Prop :=
  ∀ block, block ∈ program.allBlocks ->
    Block.SuccessorStackSignaturesChecked program block

def StackDepthBoundedBy (bound : Nat) : Nat -> List Instr -> Prop
  | depth, [] => depth <= bound
  | depth, instr :: rest =>
      depth <= bound ∧
        match Instr.stackDepthAfter? depth instr with
        | some depth' =>
            depth' <= bound ∧ StackDepthBoundedBy bound depth' rest
        | none => False

def Block.MaxStackBounded (block : Block) : Prop :=
  StackDepthBoundedBy
    (block.signature.inputDepth + block.signature.maxExtraDepth)
    block.signature.inputDepth block.body

def Program.MaxStackBounded (program : Program) : Prop :=
  ∀ block, block ∈ program.allBlocks -> block.MaxStackBounded

structure WF (program : Program) : Prop where
  labelsClosed : program.LabelsClosed
  labelsUnique : program.LabelsUnique
  functionIdsUnique : program.FunctionIdsUnique
  functionCallsClosed : program.FunctionCallsClosed
  stackSignaturesChecked : program.StackSignaturesChecked
  functionEntrySignaturesChecked : program.FunctionEntrySignaturesChecked
  successorStackSignaturesChecked : program.SuccessorStackSignaturesChecked
  maxStackBounded : program.MaxStackBounded
  pseudoInstructionsEliminable : program.BlocksPseudoFree

theorem WF.call_function_declared
    {program : Program} {block : Block}
    {functionId : FunctionId} {params returns : Nat}
    {returnLabel : Label}
    (hWF : WF program)
    (hBlock : block ∈ program.allBlocks)
    (hTerm : block.term = Term.call functionId params returns returnLabel) :
    functionId ∈ program.functionIds := by
  exact hWF.functionCallsClosed block hBlock functionId (by
    simp [Term.calledFunctionIds, hTerm])

theorem WF.call_return_label_closed
    {program : Program} {block : Block}
    {functionId : FunctionId} {params returns : Nat}
    {returnLabel : Label}
    (hWF : WF program)
    (hBlock : block ∈ program.allBlocks)
    (hTerm : block.term = Term.call functionId params returns returnLabel) :
    returnLabel ∈ program.allBlockLabels := by
  exact hWF.labelsClosed.2.2 block hBlock returnLabel (by
    simp [Term.targets, hTerm])

theorem WF.jump_target_inputDepth
    {program : Program} {block : Block} {target : Label} {depth : Nat}
    (hWF : WF program)
    (hBlock : block ∈ program.allBlocks)
    (hDepth :
      stackDepthAfter? block.signature.inputDepth block.body = some depth)
    (hTerm : block.term = Term.jump target) :
    program.labelInputDepth? target = some depth := by
  have hSucc := hWF.successorStackSignaturesChecked block hBlock
  simp [Block.SuccessorStackSignaturesChecked, hDepth,
    Term.SuccessorStackSignaturesChecked, hTerm] at hSucc
  exact hSucc

theorem WF.jumpi_targets_inputDepth
    {program : Program} {block : Block}
    {thenLabel elseLabel : Label} {depth : Nat}
    (hWF : WF program)
    (hBlock : block ∈ program.allBlocks)
    (hDepth :
      stackDepthAfter? block.signature.inputDepth block.body =
        some (depth + 1))
    (hTerm : block.term = Term.jumpi thenLabel elseLabel) :
    program.labelInputDepth? thenLabel = some depth ∧
      program.labelInputDepth? elseLabel = some depth := by
  have hSucc := hWF.successorStackSignaturesChecked block hBlock
  simp [Block.SuccessorStackSignaturesChecked, hDepth,
    Term.SuccessorStackSignaturesChecked, hTerm] at hSucc
  exact hSucc

theorem WF.switch_targets_inputDepth
    {program : Program} {block : Block}
    {cases : List (Word × Label)} {default : Label} {depth : Nat}
    (hWF : WF program)
    (hBlock : block ∈ program.allBlocks)
    (hDepth :
      stackDepthAfter? block.signature.inputDepth block.body =
        some (depth + 1))
    (hTerm : block.term = Term.switch cases default) :
    program.labelInputDepth? default = some depth ∧
      ∀ value label, (value, label) ∈ cases ->
        program.labelInputDepth? label = some depth := by
  have hSucc := hWF.successorStackSignaturesChecked block hBlock
  simp [Block.SuccessorStackSignaturesChecked, hDepth,
    Term.SuccessorStackSignaturesChecked, hTerm] at hSucc
  exact hSucc

theorem WF.call_signature_checked
    {program : Program} {block : Block}
    {functionId : FunctionId} {params returns depth : Nat}
    {returnLabel : Label}
    (hWF : WF program)
    (hBlock : block ∈ program.allBlocks)
    (hDepth :
      stackDepthAfter? block.signature.inputDepth block.body = some depth)
    (hTerm : block.term = Term.call functionId params returns returnLabel) :
    params <= depth ∧
      program.functionSignature? functionId = some (params, returns) ∧
      program.labelInputDepth? returnLabel =
        some (depth - params + returns) := by
  have hSucc := hWF.successorStackSignaturesChecked block hBlock
  simp [Block.SuccessorStackSignaturesChecked, hDepth,
    Term.SuccessorStackSignaturesChecked, hTerm] at hSucc
  exact hSucc

theorem WF.function_entry_inputDepth
    {program : Program} {function : Function}
    (hWF : WF program)
    (hFunction : function ∈ program.functions) :
    program.labelInputDepth? function.entry = some function.params :=
  hWF.functionEntrySignaturesChecked function hFunction

abbrev Behavior := L03_GeneratedYul.Behavior

def Label.entry : Label := { value := 0 }

def Label.returnBlock : Label := { value := 1 }

def StackSignature.empty : StackSignature :=
  { inputDepth := 0
    outputDepth := some 0
    maxExtraDepth := 0 }

def StackSignature.returningWith (maxExtraDepth : Nat) : StackSignature :=
  { inputDepth := 0
    outputDepth := some 1
    maxExtraDepth := maxExtraDepth }

def StackSignature.returning : StackSignature :=
  { inputDepth := 0
    outputDepth := some 1
    maxExtraDepth := 1 }

def StackSignature.returningFromStack : StackSignature :=
  { inputDepth := 1
    outputDepth := some 1
    maxExtraDepth := 0 }

def Block.stop : Block :=
  { label := Label.entry
    signature := StackSignature.empty
    body := []
    term := Term.stop }

def Block.returnCode (code : List Instr) : Block :=
  { label := Label.entry
    signature := StackSignature.returningWith code.length
    body := code
    term := Term.returnOp }

def Block.jumpCode (label target : Label) (code : List Instr) : Block :=
  { label := label
    signature := StackSignature.returningWith code.length
    body := code
    term := Term.jump target }

def Block.returnFromStack (label : Label) : Block :=
  { label := label
    signature := StackSignature.returningFromStack
    body := []
    term := Term.returnOp }

def Block.returnWord (value : Word) : Block :=
  Block.returnCode [Instr.push (Atom.word value)]

def Block.returnWord0 : Block :=
  Block.returnWord 0

def Block.returnWord3 : Block :=
  Block.returnWord 3

def Program.stop : Program :=
  { entry := Label.entry
    blocks := [Block.stop]
    functions := [] }

def Program.returnCode (code : List Instr) : Program :=
  { entry := Label.entry
    blocks := [Block.returnCode code]
    functions := [] }

def Program.jumpReturnCode (code : List Instr) : Program :=
  { entry := Label.entry
    blocks :=
      [ Block.jumpCode Label.entry Label.returnBlock code
      , Block.returnFromStack Label.returnBlock ]
    functions := [] }

def Program.returnWord (value : Word) : Program :=
  Program.returnCode [Instr.push (Atom.word value)]

def Program.returnWord0 : Program :=
  Program.returnWord 0

def Program.returnWord3 : Program :=
  Program.returnWord 3

def Program.IsStop (program : Program) : Prop :=
  program.entry = Label.entry ∧ program.blocks = [Block.stop] ∧
    program.functions = []

def Program.IsReturnCode (program : Program) (code : List Instr) : Prop :=
  program.entry = Label.entry ∧ program.blocks = [Block.returnCode code] ∧
    program.functions = []

def Program.IsReturnWord (program : Program) (value : Word) : Prop :=
  program.entry = Label.entry ∧ program.blocks = [Block.returnWord value] ∧
    program.functions = []

def Program.IsReturnWord0 (program : Program) : Prop :=
  program.IsReturnWord 0

def Program.IsReturnWord3 (program : Program) : Prop :=
  program.IsReturnWord 3

inductive Config where
  | at : Label -> List Word -> Config
  | halted
  | returnedWord : Word -> Config
  | stuck : Label -> Config
  deriving Repr

def replaceAt? {α : Type} : List α -> Nat -> α -> Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value =>
      match replaceAt? rest index value with
      | some rest' => some (head :: rest')
      | none => none

def execInstr (stack : List Word) : Instr -> Option (List Word)
  | Instr.push (Atom.word value) => some (value :: stack)
  | Instr.dup index =>
      match stack[index]? with
      | some value => some (value :: stack)
      | none => none
  | Instr.swap index =>
      match stack with
      | [] => none
      | top :: rest =>
          match rest[index]? with
          | some target =>
              match replaceAt? rest index top with
              | some rest' => some (target :: rest')
              | none => none
          | none => none
  | Instr.pop =>
      match stack with
      | [] => none
      | _ :: rest => some rest
  | Instr.op PrimOp.add =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.addWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.mul =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.mulWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.div =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.divWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.signextend =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.signextendWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.modOp =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.modWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.sub =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.subWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.eq =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.eqWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.lt =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.ltWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.gt =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.gtWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.andOp =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.andWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.orOp =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.orWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.xor =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.xorWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.byteOp =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.byteWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.shl =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.shlWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.shr =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.shrWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.sar =>
      match stack with
      | rhs :: lhs :: rest => some (SharedSemantics.sarWord lhs rhs :: rest)
      | _ => none
  | Instr.op PrimOp.iszero =>
      match stack with
      | value :: rest => some (SharedSemantics.iszeroWord value :: rest)
      | _ => none
  | Instr.op PrimOp.notOp =>
      match stack with
      | value :: rest => some (SharedSemantics.notWord value :: rest)
      | _ => none
  | _ => none

def execInstrs : List Word -> List Instr -> Option (List Word)
  | stack, [] => some stack
  | stack, instr :: rest => do
      let stack' ← execInstr stack instr
      execInstrs stack' rest

theorem InstrsPseudoFree_nil : InstrsPseudoFree [] := by
  intro instr hMem
  cases hMem

theorem InstrsPseudoFree_append {pre post : List Instr}
    (hPre : InstrsPseudoFree pre) (hPost : InstrsPseudoFree post) :
    InstrsPseudoFree (pre ++ post) := by
  intro instr hMem
  rw [List.mem_append] at hMem
  cases hMem with
  | inl h => exact hPre instr h
  | inr h => exact hPost instr h

theorem InstrsPseudoFree_singleton_push (atom : Atom) :
    InstrsPseudoFree [Instr.push atom] := by
  intro instr hMem
  simp at hMem
  cases hMem
  trivial

theorem InstrsPseudoFree_singleton_dup (index : Nat) :
    InstrsPseudoFree [Instr.dup index] := by
  intro instr hMem
  simp at hMem
  cases hMem
  trivial

theorem InstrsPseudoFree_singleton_swap (index : Nat) :
    InstrsPseudoFree [Instr.swap index] := by
  intro instr hMem
  simp at hMem
  cases hMem
  trivial

theorem InstrsPseudoFree_singleton_pop :
    InstrsPseudoFree [Instr.pop] := by
  intro instr hMem
  simp at hMem
  cases hMem
  trivial

theorem InstrsPseudoFree_singleton_op (op : PrimOp) :
    InstrsPseudoFree [Instr.op op] := by
  intro instr hMem
  simp at hMem
  cases hMem
  trivial

theorem stackDepthAfter?_append
    (pre post : List Instr) (depth : Nat) :
    stackDepthAfter? depth (pre ++ post) =
      match stackDepthAfter? depth pre with
      | some depth' => stackDepthAfter? depth' post
      | none => none := by
  induction pre generalizing depth with
  | nil =>
      simp [stackDepthAfter?]
  | cons instr rest ih =>
      simp [stackDepthAfter?]
      cases Instr.stackDepthAfter? depth instr <;> simp [ih]

theorem Instr.stackDepthAfter?_le_succ
    {depth : Nat} {instr : Instr} {depth' : Nat}
    (hDepth : instr.stackDepthAfter? depth = some depth') :
    depth' <= depth + 1 := by
  cases instr with
  | push atom =>
      simp [Instr.stackDepthAfter?] at hDepth
      cases hDepth
      exact Nat.le_refl (depth + 1)
  | dup index =>
      by_cases hIndex : index < depth
      · simp [Instr.stackDepthAfter?, hIndex] at hDepth
        cases hDepth
        omega
      · simp [Instr.stackDepthAfter?, hIndex] at hDepth
  | swap index =>
      by_cases hIndex : index + 1 < depth
      · simp [Instr.stackDepthAfter?, hIndex] at hDepth
        cases hDepth
        omega
      · simp [Instr.stackDepthAfter?, hIndex] at hDepth
  | pop =>
      cases depth with
      | zero =>
          simp [Instr.stackDepthAfter?] at hDepth
      | succ depth =>
          simp [Instr.stackDepthAfter?] at hDepth
          cases hDepth
          omega
  | op op =>
      cases depth with
      | zero =>
          cases op <;> simp [Instr.stackDepthAfter?] at hDepth
      | succ depth =>
          cases depth with
          | zero =>
              cases op <;> simp [Instr.stackDepthAfter?] at hDepth ⊢
              all_goals omega
          | succ depth =>
              cases op <;> simp [Instr.stackDepthAfter?] at hDepth ⊢
              all_goals omega
  | env op =>
      simp [Instr.stackDepthAfter?] at hDepth
  | pseudo instr =>
      simp [Instr.stackDepthAfter?] at hDepth

theorem StackDepthBoundedBy.mono
    {low high depth : Nat} {code : List Instr}
    (hLe : low <= high)
    (hBound : StackDepthBoundedBy low depth code) :
    StackDepthBoundedBy high depth code := by
  induction code generalizing depth with
  | nil =>
      simp [StackDepthBoundedBy] at hBound ⊢
      exact Nat.le_trans hBound hLe
  | cons instr rest ih =>
      simp [StackDepthBoundedBy] at hBound ⊢
      rcases hBound with ⟨hDepth, hRest⟩
      refine ⟨Nat.le_trans hDepth hLe, ?_⟩
      cases hInstr : Instr.stackDepthAfter? depth instr with
      | none =>
          simp [hInstr] at hRest
      | some depth' =>
          simp [hInstr] at hRest ⊢
          exact
            ⟨Nat.le_trans hRest.1 hLe,
              ih hRest.2⟩

theorem stackDepthBoundedBy_length
    {code : List Instr} {depth final : Nat}
    (hDepth : stackDepthAfter? depth code = some final) :
    StackDepthBoundedBy (depth + code.length) depth code := by
  induction code generalizing depth final with
  | nil =>
      simp [stackDepthAfter?, StackDepthBoundedBy] at hDepth ⊢
  | cons instr rest ih =>
      simp [stackDepthAfter?] at hDepth
      cases hInstr : Instr.stackDepthAfter? depth instr with
      | none =>
          simp [hInstr] at hDepth
      | some depth' =>
          simp [hInstr] at hDepth
          have hRestBound := ih hDepth
          have hStep := Instr.stackDepthAfter?_le_succ hInstr
          have hRestLe :
              depth' + rest.length <= depth + (instr :: rest).length := by
            simp
            omega
          have hRestBoundHigh :=
            StackDepthBoundedBy.mono hRestLe hRestBound
          show
            depth <= depth + (instr :: rest).length ∧
              (match Instr.stackDepthAfter? depth instr with
              | some depth'' =>
                  depth'' <= depth + (instr :: rest).length ∧
                    StackDepthBoundedBy (depth + (instr :: rest).length)
                      depth'' rest
              | none => False)
          refine ⟨by simp, ?_⟩
          simp [hInstr]
          exact ⟨by omega, hRestBoundHigh⟩

theorem stackDepthAfter?_singleton_push
    (atom : Atom) (depth : Nat) :
    stackDepthAfter? depth [Instr.push atom] = some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_dup
    {index depth : Nat} (hIndex : index < depth) :
    stackDepthAfter? depth [Instr.dup index] = some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?, hIndex]

theorem stackDepthAfter?_singleton_swap
    {index depth : Nat} (hIndex : index + 1 < depth) :
    stackDepthAfter? depth [Instr.swap index] = some depth := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?, hIndex]

theorem stackDepthAfter?_singleton_pop (depth : Nat) :
    stackDepthAfter? (depth + 1) [Instr.pop] = some depth := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_add (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.add] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_mul (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.mul] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_div (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.div] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_signextend (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.signextend] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_mod (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.modOp] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_sub (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.sub] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_eq (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.eq] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_lt (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.lt] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_gt (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.gt] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_and (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.andOp] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_or (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.orOp] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_xor (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.xor] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_byte (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.byteOp] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_shl (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.shl] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_shr (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.shr] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_sar (depth : Nat) :
    stackDepthAfter? (depth + 2) [Instr.op PrimOp.sar] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_iszero (depth : Nat) :
    stackDepthAfter? (depth + 1) [Instr.op PrimOp.iszero] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem stackDepthAfter?_singleton_not (depth : Nat) :
    stackDepthAfter? (depth + 1) [Instr.op PrimOp.notOp] =
      some (depth + 1) := by
  simp [stackDepthAfter?, Instr.stackDepthAfter?]

theorem execInstr_pop_cons (value : Word) (stack : List Word) :
    execInstr (value :: stack) Instr.pop = some stack := by
  rfl

theorem execInstr_dup_get?
    {stack : List Word} {index : Nat} {value : Word}
    (hGet : stack[index]? = some value) :
    execInstr stack (Instr.dup index) = some (value :: stack) := by
  simp [execInstr, hGet]

theorem execInstr_dup_top (value : Word) (stack : List Word) :
    execInstr (value :: stack) (Instr.dup 0) =
      some (value :: value :: stack) := by
  rfl

theorem execInstr_swap_top_next
    (top next : Word) (stack : List Word) :
    execInstr (top :: next :: stack) (Instr.swap 0) =
      some (next :: top :: stack) := by
  rfl

theorem execInstr_pop_nil :
    execInstr [] Instr.pop = none := by
  rfl

theorem execInstrs_push_pop (value : Word) (stack : List Word) :
    execInstrs stack
      [Instr.push (Atom.word value), Instr.pop] = some stack := by
  simp [execInstrs, execInstr]

theorem execInstrs_push_dup_add (value : Word) (stack : List Word) :
    execInstrs stack
      [ Instr.push (Atom.word value)
      , Instr.dup 0
      , Instr.op PrimOp.add ] =
        some (SharedSemantics.addWord value value :: stack) := by
  simp [execInstrs, execInstr]

theorem execInstrs_append
    (pre post : List Instr) (stack : List Word) :
    execInstrs stack (pre ++ post) =
      match execInstrs stack pre with
      | some stack' => execInstrs stack' post
      | none => none := by
  induction pre generalizing stack with
  | nil =>
      simp [execInstrs]
  | cons instr rest ih =>
      simp [execInstrs]
      cases execInstr stack instr <;> simp [ih]

def execTerm (current : Label) (stack : List Word) : Term -> Config
  | Term.jump label => Config.at label stack
  | Term.jumpi thenLabel elseLabel =>
      match stack with
      | condition :: rest =>
          if SharedSemantics.norm condition == 0 then
            Config.at elseLabel rest
          else
            Config.at thenLabel rest
      | [] => Config.stuck current
  | Term.switch cases default =>
      match stack with
      | value :: rest =>
          let target :=
            match cases.find? (fun c => SharedSemantics.norm c.fst == SharedSemantics.norm value) with
            | some branch => branch.snd
            | none => default
          Config.at target rest
      | [] => Config.stuck current
  | Term.stop => Config.halted
  | Term.returnOp =>
      match stack with
      | value :: _ => Config.returnedWord value
      | [] => Config.stuck current
  | Term.revert => Config.halted
  | Term.invalid => Config.halted
  | _ => Config.stuck current

def step (program : Program) : Config -> Config
  | Config.at label stack =>
      match lookupBlock? program.allBlocks label with
      | some block =>
          match execInstrs stack block.body with
          | some stack => execTerm label stack block.term
          | none => Config.stuck label
      | none => Config.stuck label
  | config => config

theorem step_jump_block
    {program : Program} {label target : Label} {block : Block}
    {stack stack' : List Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some stack')
    (hTerm : block.term = Term.jump target) :
    step program (Config.at label stack) = Config.at target stack' := by
  simp [step, hLookup, hExec, hTerm, execTerm]

theorem step_jumpi_zero_block
    {program : Program} {label thenLabel elseLabel : Label} {block : Block}
    {stack rest : List Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some (0 :: rest))
    (hTerm : block.term = Term.jumpi thenLabel elseLabel) :
    step program (Config.at label stack) = Config.at elseLabel rest := by
  simp [step, hLookup, hExec, hTerm, execTerm,
    SharedSemantics.norm, SharedSemantics.wordModulus]

theorem step_jumpi_one_block
    {program : Program} {label thenLabel elseLabel : Label} {block : Block}
    {stack rest : List Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some (1 :: rest))
    (hTerm : block.term = Term.jumpi thenLabel elseLabel) :
    step program (Config.at label stack) = Config.at thenLabel rest := by
  simp [step, hLookup, hExec, hTerm, execTerm,
    SharedSemantics.norm, SharedSemantics.wordModulus]

theorem step_switch_zero_block
    {program : Program} {label caseLabel defaultLabel : Label} {block : Block}
    {stack rest : List Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some (0 :: rest))
    (hTerm : block.term = Term.switch [(0, caseLabel)] defaultLabel) :
    step program (Config.at label stack) = Config.at caseLabel rest := by
  simp [step, hLookup, hExec, hTerm, execTerm,
    SharedSemantics.norm, SharedSemantics.wordModulus]

theorem step_switch_default_one_block
    {program : Program} {label caseLabel defaultLabel : Label} {block : Block}
    {stack rest : List Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some (1 :: rest))
    (hTerm : block.term = Term.switch [(0, caseLabel)] defaultLabel) :
    step program (Config.at label stack) = Config.at defaultLabel rest := by
  simp [step, hLookup, hExec, hTerm, execTerm,
    SharedSemantics.norm, SharedSemantics.wordModulus]

theorem step_stop_block
    {program : Program} {label : Label} {block : Block}
    {stack stack' : List Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some stack')
    (hTerm : block.term = Term.stop) :
    step program (Config.at label stack) = Config.halted := by
  simp [step, hLookup, hExec, hTerm, execTerm]

theorem step_return_block
    {program : Program} {label : Label} {block : Block}
    {stack rest : List Word} {value : Word}
    (hLookup : lookupBlock? program.allBlocks label = some block)
    (hExec : execInstrs stack block.body = some (value :: rest))
    (hTerm : block.term = Term.returnOp) :
    step program (Config.at label stack) = Config.returnedWord value := by
  simp [step, hLookup, hExec, hTerm, execTerm]

inductive Reaches (program : Program) : Config -> Config -> Prop where
  | refl {config : Config} :
      Reaches program config config
  | one {start finish : Config} :
      step program start = finish ->
      Reaches program start finish
  | trans {start middle finish : Config} :
      Reaches program start middle ->
      Reaches program middle finish ->
      Reaches program start finish

inductive Semantics : Program -> Behavior -> Prop where
  | reachesStop {program : Program} :
      program.IsStop ->
      Reaches program (Config.at program.entry []) Config.halted ->
      Semantics program L01_ValidSolidity.Behavior.stopped
  | reachesReturnWord0 {program : Program} :
      program.IsReturnWord0 ->
      Reaches program (Config.at program.entry []) (Config.returnedWord 0) ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord 0)
  | reachesReturnWord3 {program : Program} :
      program.IsReturnWord3 ->
      Reaches program (Config.at program.entry []) (Config.returnedWord 3) ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord 3)
  | reachesReturnWord {program : Program} {value : Word} :
      program.IsReturnWord value ->
      Reaches program (Config.at program.entry []) (Config.returnedWord value) ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord value)
  | reachesReturnCode {program : Program} {code : List Instr}
      {value : Word} {stack : List Word} :
      program.IsReturnCode code ->
      execInstrs [] code = some (value :: stack) ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord value)

theorem Program.stop_isStop : Program.stop.IsStop := by
  simp [Program.stop, Program.IsStop]

theorem Program.stop_wf : WF Program.stop := by
      exact
    { labelsClosed := by
        simp [Program.LabelsClosed, Program.allBlockLabels,
          Program.allBlocks, Program.functionBlocks,
          Program.stop, Block.stop, Term.targets]
      labelsUnique := by
        simp [Program.LabelsUnique, Program.allBlockLabels,
          Program.allBlocks, Program.functionBlocks,
          Program.stop, Block.stop]
      functionIdsUnique := by
        simp [Program.FunctionIdsUnique, Program.functionIds, Program.stop]
      functionCallsClosed := by
        intro block hMem functionId hCall
        simp [Program.stop, Block.stop, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Term.calledFunctionIds] at hCall
      stackSignaturesChecked := by
        intro block hMem
        simp [Program.stop, Block.stop, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Block.StackSignatureChecked, StackSignature.empty,
          stackDepthAfter?, Term.StackInputChecked]
      functionEntrySignaturesChecked := by
        intro function hMem
        simp [Program.stop] at hMem
      successorStackSignaturesChecked := by
        intro block hMem
        simp [Program.stop, Block.stop, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Block.SuccessorStackSignaturesChecked, StackSignature.empty,
          stackDepthAfter?, Term.SuccessorStackSignaturesChecked]
      maxStackBounded := by
        intro block hMem
        simp [Program.stop, Block.stop, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Block.MaxStackBounded, StackDepthBoundedBy,
          StackSignature.empty]
      pseudoInstructionsEliminable := by
        intro block hMem
        simp [Program.stop, Block.stop, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        exact InstrsPseudoFree_nil }

theorem Program.stop_reaches :
    Reaches Program.stop (Config.at Program.stop.entry []) Config.halted := by
  apply Reaches.one
  simp [Program.stop, Block.stop, Program.allBlocks,
    Program.functionBlocks, step, execTerm]
  rfl

theorem Program.stop_semantics :
    Semantics Program.stop L01_ValidSolidity.Behavior.stopped := by
  exact Semantics.reachesStop Program.stop_isStop Program.stop_reaches

theorem Program.stop_blocksPseudoFree :
    Program.stop.BlocksPseudoFree := by
  intro block hMem
  simp [Program.stop, Block.stop, Program.allBlocks,
    Program.functionBlocks] at hMem
  cases hMem
  exact InstrsPseudoFree_nil

theorem Program.stop_not_isReturnCode {code : List Instr} :
    ¬ Program.stop.IsReturnCode code := by
  intro hReturn
  rcases hReturn with ⟨_hEntry, hBlocks, _hFunctions⟩
  simp [Program.stop, Block.stop, Block.returnCode] at hBlocks

theorem Program.returnWord0_isReturnWord0 :
    Program.returnWord0.IsReturnWord0 := by
  simp [Program.returnWord0, Program.returnWord, Program.returnCode,
    Program.IsReturnWord0, Program.IsReturnWord, Block.returnWord,
    Block.returnCode]

theorem Program.returnWord_isReturnWord (value : Word) :
    (Program.returnWord value).IsReturnWord value := by
  simp [Program.returnWord, Program.returnCode, Program.IsReturnWord,
    Block.returnWord, Block.returnCode]

theorem Program.returnCode_isReturnCode (code : List Instr) :
    (Program.returnCode code).IsReturnCode code := by
  simp [Program.returnCode, Program.IsReturnCode]

theorem Program.returnCode_wf {code : List Instr}
    (hCode : InstrsPseudoFree code)
    (hDepth : stackDepthAfter? 0 code = some 1) :
    WF (Program.returnCode code) := by
  exact
    { labelsClosed := by
        simp [Program.LabelsClosed, Program.allBlockLabels,
          Program.allBlocks, Program.functionBlocks,
          Program.returnCode, Block.returnCode, Term.targets]
      labelsUnique := by
        simp [Program.LabelsUnique, Program.allBlockLabels,
          Program.allBlocks, Program.functionBlocks,
          Program.returnCode, Block.returnCode]
      functionIdsUnique := by
        simp [Program.FunctionIdsUnique, Program.functionIds,
          Program.returnCode]
      functionCallsClosed := by
        intro block hMem functionId hCall
        simp [Program.returnCode, Block.returnCode, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Term.calledFunctionIds] at hCall
      stackSignaturesChecked := by
        intro block hMem
        simp [Program.returnCode, Block.returnCode, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Block.StackSignatureChecked, StackSignature.returningWith, hDepth,
          Term.StackInputChecked]
      functionEntrySignaturesChecked := by
        intro function hMem
        simp [Program.returnCode] at hMem
      successorStackSignaturesChecked := by
        intro block hMem
        simp [Program.returnCode, Block.returnCode, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simp [Block.SuccessorStackSignaturesChecked,
          StackSignature.returningWith, hDepth,
          Term.SuccessorStackSignaturesChecked]
      maxStackBounded := by
        intro block hMem
        simp [Program.returnCode, Block.returnCode, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        simpa [Block.MaxStackBounded, StackSignature.returningWith] using
          stackDepthBoundedBy_length hDepth
      pseudoInstructionsEliminable := by
        intro block hMem
        simp [Program.returnCode, Block.returnCode, Program.allBlocks,
          Program.functionBlocks] at hMem
        cases hMem
        exact hCode }

theorem Program.jumpReturnCode_wf {code : List Instr}
    (hCode : InstrsPseudoFree code)
    (hDepth : stackDepthAfter? 0 code = some 1) :
    WF (Program.jumpReturnCode code) := by
  exact
    { labelsClosed := by
        simp [Program.LabelsClosed, Program.allBlockLabels,
          Program.allBlocks, Program.functionBlocks,
          Program.jumpReturnCode, Block.jumpCode, Block.returnFromStack,
          Term.targets, Label.entry, Label.returnBlock]
      labelsUnique := by
        simp [Program.LabelsUnique, Program.allBlockLabels,
          Program.allBlocks, Program.functionBlocks,
          Program.jumpReturnCode, Block.jumpCode, Block.returnFromStack,
          Label.entry, Label.returnBlock]
      functionIdsUnique := by
        simp [Program.FunctionIdsUnique, Program.functionIds,
          Program.jumpReturnCode]
      functionCallsClosed := by
        intro block hMem functionId hCall
        simp [Program.jumpReturnCode, Block.jumpCode,
          Block.returnFromStack, Program.allBlocks,
          Program.functionBlocks] at hMem
        rcases hMem with hBlock | hBlock
        · cases hBlock
          simp [Term.calledFunctionIds] at hCall
        · cases hBlock
          simp [Term.calledFunctionIds] at hCall
      stackSignaturesChecked := by
        intro block hMem
        simp [Program.jumpReturnCode, Block.jumpCode,
          Block.returnFromStack, Program.allBlocks,
          Program.functionBlocks] at hMem
        rcases hMem with hBlock | hBlock
        · cases hBlock
          simp [Block.StackSignatureChecked, StackSignature.returningWith,
            hDepth, Term.StackInputChecked]
        · cases hBlock
          simp [Block.StackSignatureChecked,
            StackSignature.returningFromStack,
            stackDepthAfter?, Term.StackInputChecked]
      functionEntrySignaturesChecked := by
        intro function hMem
        simp [Program.jumpReturnCode] at hMem
      successorStackSignaturesChecked := by
        intro block hMem
        simp [Program.jumpReturnCode, Block.jumpCode,
          Block.returnFromStack, Program.allBlocks,
          Program.functionBlocks] at hMem
        rcases hMem with hBlock | hBlock
        · cases hBlock
          simp [Block.SuccessorStackSignaturesChecked,
            StackSignature.returningWith, hDepth,
            Term.SuccessorStackSignaturesChecked,
            Program.labelInputDepth?, Program.allBlocks,
            Program.functionBlocks, Program.jumpReturnCode,
            Block.jumpCode, Block.returnFromStack, lookupBlock?,
            Label.entry, Label.returnBlock,
            StackSignature.returningFromStack]
        · cases hBlock
          simp [Block.SuccessorStackSignaturesChecked,
            StackSignature.returningFromStack, stackDepthAfter?,
            Term.SuccessorStackSignaturesChecked]
      maxStackBounded := by
        intro block hMem
        simp [Program.jumpReturnCode, Block.jumpCode,
          Block.returnFromStack, Program.allBlocks,
          Program.functionBlocks] at hMem
        rcases hMem with hBlock | hBlock
        · cases hBlock
          simpa [Block.MaxStackBounded, StackSignature.returningWith] using
            stackDepthBoundedBy_length hDepth
        · cases hBlock
          simp [Block.MaxStackBounded,
            StackSignature.returningFromStack, StackDepthBoundedBy]
      pseudoInstructionsEliminable := by
        intro block hMem
        simp [Program.jumpReturnCode, Block.jumpCode,
          Block.returnFromStack, Program.allBlocks,
          Program.functionBlocks] at hMem
        rcases hMem with hBlock | hBlock
        · cases hBlock
          exact hCode
        · cases hBlock
          exact InstrsPseudoFree_nil
        }

theorem Program.returnCode_blocksPseudoFree {code : List Instr}
    (hCode : InstrsPseudoFree code) :
    (Program.returnCode code).BlocksPseudoFree := by
  intro block hMem
  simp [Program.returnCode, Block.returnCode, Program.allBlocks,
    Program.functionBlocks] at hMem
  cases hMem
  exact hCode

theorem Program.returnCode_isReturnCode_code_eq
    {actual expected : List Instr}
    (hReturn : (Program.returnCode actual).IsReturnCode expected) :
    expected = actual := by
  rcases hReturn with ⟨_hEntry, hBlocks, _hFunctions⟩
  simp [Program.returnCode, Block.returnCode] at hBlocks
  exact hBlocks.2.symm

theorem Program.returnWord_wf (value : Word) : WF (Program.returnWord value) := by
  exact Program.returnCode_wf
    (InstrsPseudoFree_singleton_push (Atom.word value))
    (by
      simpa using
        stackDepthAfter?_singleton_push (Atom.word value) 0)

theorem Program.returnWord0_wf : WF Program.returnWord0 := by
  exact Program.returnWord_wf 0

theorem Program.returnWord_reaches (value : Word) :
    Reaches (Program.returnWord value)
      (Config.at (Program.returnWord value).entry [])
      (Config.returnedWord value) := by
  apply Reaches.one
  simp [Program.returnWord, Program.returnCode, Block.returnCode,
    Program.allBlocks, Program.functionBlocks, Label.entry, lookupBlock?, step,
    execInstrs, execInstr, execTerm]

theorem Program.returnCode_reaches
    {code : List Instr} {value : Word} {stack : List Word}
    (hExec : execInstrs [] code = some (value :: stack)) :
    Reaches (Program.returnCode code)
      (Config.at (Program.returnCode code).entry [])
      (Config.returnedWord value) := by
  apply Reaches.one
  simp [Program.returnCode, Block.returnCode, Program.allBlocks,
    Program.functionBlocks, Label.entry, lookupBlock?, step, hExec, execTerm]

theorem Program.jumpReturnCode_reaches
    {code : List Instr} {value : Word} {stack : List Word}
    (hExec : execInstrs [] code = some (value :: stack)) :
    Reaches (Program.jumpReturnCode code)
      (Config.at (Program.jumpReturnCode code).entry [])
      (Config.returnedWord value) := by
  exact Reaches.trans
    (middle := Config.at Label.returnBlock (value :: stack))
    (by
      apply Reaches.one
      simp [Program.jumpReturnCode, Block.jumpCode, Block.returnFromStack,
        Program.allBlocks, Program.functionBlocks, Label.entry,
        Label.returnBlock, lookupBlock?, step, hExec, execTerm])
    (by
      apply Reaches.one
      simp [Program.jumpReturnCode, Block.jumpCode, Block.returnFromStack,
        Program.allBlocks, Program.functionBlocks, Label.entry,
        Label.returnBlock, lookupBlock?, step, execInstrs, execTerm])

theorem Program.returnWord0_reaches :
    Reaches Program.returnWord0
      (Config.at Program.returnWord0.entry []) (Config.returnedWord 0) := by
  exact Program.returnWord_reaches 0

theorem Program.returnWord_semantics (value : Word) :
    Semantics (Program.returnWord value)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.reachesReturnWord (Program.returnWord_isReturnWord value)
    (Program.returnWord_reaches value)

theorem Program.returnCode_semantics
    {code : List Instr} {value : Word} {stack : List Word}
    (hExec : execInstrs [] code = some (value :: stack)) :
    Semantics (Program.returnCode code)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.reachesReturnCode
    (Program.returnCode_isReturnCode code) hExec

theorem Program.returnWord0_semantics :
    Semantics Program.returnWord0
      (L01_ValidSolidity.Behavior.returnedWord 0) := by
  exact Program.returnWord_semantics 0

theorem Program.returnWord3_isReturnWord3 :
    Program.returnWord3.IsReturnWord3 := by
  simp [Program.returnWord3, Program.returnWord, Program.returnCode,
    Program.IsReturnWord3, Program.IsReturnWord, Block.returnWord,
    Block.returnCode]

theorem Program.returnWord3_wf : WF Program.returnWord3 := by
  exact Program.returnWord_wf 3

theorem Program.returnWord3_reaches :
    Reaches Program.returnWord3
      (Config.at Program.returnWord3.entry []) (Config.returnedWord 3) := by
  exact Program.returnWord_reaches 3

theorem Program.returnWord3_semantics :
    Semantics Program.returnWord3
      (L01_ValidSolidity.Behavior.returnedWord 3) := by
  exact Program.returnWord_semantics 3

end L04_StackCfg
end Spine
end SolidCore
