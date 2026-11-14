# factory lane: createPair in the frontend (E1 fragment) and its source building blocks

Base: solidity-lean alpharush/certified-translation 9fb89ee. Head: lane/create2 429b812
(sl-factory-create2.bundle = 9fb89ee..429b812; the same three commits as patches 0001-0003).
Apply: git fetch sl-factory-create2.bundle lane/create2:lane/create2 (or git am 000*.patch).
Earlier pre-reset work: wip/ (unchanged).

## What changed

- Frontend (scripts/solc_ast_to_lean_source.py): translates exactly one inline assembly block,
  target := create2(value, add(code, 32), mload(code), salt), with every identifier a Solidity
  local (address target, bytes memory code, value a Yul number or uint256 local, salt a Yul
  number, uint256 or bytes32 local), to the new Ast statement Stmt.assemblyCreate2. Every other
  block still fails the node guard (10 negatives in scripts/verify/create2_sources.py: offset 64,
  create, mload of another local, two statements, Yul local, bytes16 salt, uint8 value,
  callvalue() operand, bytes-memory target, uint256 target: all refused).
- Type checker: checkAssemblyCreate2 (the operand rules above, locals only), and creation is
  refused in view/pure functions (requireLogOrCreateAllowed).
- Semantics (Interpreter.lean): core Expr.create2Bytes value code salt = one Query.external
  CREATE2 request from self whose init code is the bytes of code (create2BytesRequest; not the
  name encoding that new C{salt}() uses), returning the answered address, 0 on failure, never
  reverting the caller. Yul right-to-left operand order (salt, code, value).
  type(UniswapV2Pair).creationCode stays the context's contractCreationCodes entry.
- uniswap_v2_sources.py: Factory no longer omits createPair (no --omit-function).
- uniswap_v2_core.py: UniswapV2Factory joins STAGED (see receipts: one-declaration check hits
  the 6 GB cap); lakefile lib ContractsUniswapV2Factory + CI step; gen.sh checks Factory/Contract.lean.
- SolidCore/Refinement/Generic/CreateNode.lean (E3 building block, as CallNode is for calls).

## Proved (kernel; axioms printed, only propext, Classical.choice, Quot.sound)

| theorem | statement | axioms |
|---|---|---|
| SolidCore.Verify.VC.UniswapV2Factory.contract_ok (Factory/Contract.lean) | the full Factory source, createPair included, type checks and translates (createPair is p0_1 of Fn/UniswapV2Factory_allPairsLength.lean, kernel_some) | propext, Classical.choice, Quot.sound |
| SolidCore.Refinement.CreateNode.eval_create2Bytes | Expr.evalFuel (n+1) of create2Bytes v c s, given operand evaluations without requests, = .request (.external (snapshotWorld ctx st) (.create (create2BytesRequest ctx code value salt))) (fun resp => pure (word resp.address, adopted world)) | propext, Classical.choice, Quot.sound |
| SolidCore.Refinement.CreateNode.answer_word | under EvmCreate2 req resp (the environment answers 0 or EIP-1014's address = EthLib create2Address of creator, salt, init code), create2Bytes returns 0 or create2Word self salt code | propext, Classical.choice, Quot.sound |
| SolidCore.Refinement.CreateNode.evmCreate2_failed | EvmCreate2 holds of the default (failed) answer: the premise is satisfiable | propext, Quot.sound |

Premise EvmCreate2 is about the open world's answer, not the hash: no collision-freedom premise.

## Execution tests (#guard, compiled evaluation, NOT kernel theorems)

- Contracts/UniswapV2/Factory/Create2Run.lean, createPair(0xb2, 0xa1) on SolidCore's checked Factory:
  request 1 = CREATE2 from the factory, init code = context creation code, value 0,
  salt = keccak256(abi.encodePacked(0xa1, 0xb2)) = 0x40574bd1...2ee9 (matches cast keccak);
  request 2 = initialize(0xa1, 0xb2) (0x485cc955) to the answered address; result: returns the
  pair, getPair both ways and allPairs[0] = pair, allPairs.length = 1 (slots match cast keccak),
  exactly 4 slots written, one PairCreated(0xa1, 0xb2, pair, 1).
  Negatives: createPair(B, A) asks the same creation; a failed creation (address 0) reverts with
  empty data (initialize to a code-less address); identical tokens revert before any request.
- Contracts/Create2/Run.lean (MIT test contract Deployer.sol): literal and argument operands,
  failed creation returns 0 without revert; negatives: other salt != recorded request; deploy
  declared view is refused by the checker (mutabilityViolation).
- A kernel (decide +kernel) version of the Deployer tests did not reduce (selector Keccak needs
  the kernel_rfl tables); not delivered.

## Neutrality

Frontend at 9fb89ee vs lane on the generated sources: UniswapV2ERC20 (23134 B) and UniswapV2Pair
(83523 B) translations byte-identical; Factory: the base frontend refuses the file (InlineAssembly),
the lane frontend translates it.

## Receipts (14 GB Hand, LEAN_NUM_THREADS=1, Lean v4.35, solc 0.8.35 sha256 fa8ac9a3...)

| command | exit | wall | peak RSS |
|---|---|---|---|
| SOLC=solc bash scripts/verify/uniswap_v2_gen.sh | 0 | 2 s | - |
| uniswap_v2_sources.py --check / uniswap_v2_core.py --check / create2_sources.py --check | 0 / 0 / 0 | - | - |
| lean -M 6000 Contracts/UniswapV2/Factory/Core.lean (unstaged, one declaration) | 1 (kernel excessive memory at translated_eq) | 144 s | 6002 MB |
| lake build -KleanMemory=6000 ContractsUniswapV2Factory ContractsUniswapV2 (staged) | 0 | 490 s | 5489 MB (largest stage Ctx, 213 s) |
| lean -M 6000 Contracts/UniswapV2/Factory/Create2Run.lean | 0 | 25 s | 2363 MB |
| lean -M 6000 SolidCore/Refinement/Generic/CreateNode.lean | 0 | 4 s | 1997 MB |
| lean -M 6000 Contracts/Create2/Run.lean | 0 | 3 s | 2044 MB |
| lake env lean (print axioms of the 4 theorems above) | 0 | - | - |

Peak RSS = RUSAGE_CHILDREN max RSS (largest single process) via a wrapper.

## Not done / blocking CERTIFIED for createPair

- E3 for createPair: Generic.check has no creation node; the source-to-MIR check needs a
  Tree/WExpr leaf for the CREATE2 request (CreateNode.eval_create2Bytes is the source half) and the
  MIR side's creation op. Not started.
- E4-E8 for createPair not attempted on this base.
- Regression of other CI libraries over the Ast/Interpreter change: see the update below (pending
  at this checkpoint).
