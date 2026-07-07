# BC soundness-audit probes

Audit artifacts. NOT wired into `manifest.json`. Ground truth: pinned solc
`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`, Forge
`/Users/dan/.foundry/bin/forge`.

## Driver: `drive.py`

Each `lake env lean` run costs ~30s (import-chain elaboration). AMORTIZE: put
many probe functions in ONE `.sol`, run ONE `eval` with MANY exprs.

```
# accept/reject: solc --bin vs our import+typecheck
python3 tests/bc-audit-probes/drive.py accept <sol> <Contract>

# execution values: import + run #eval exprs (our side). solc line = accept/reject only.
python3 tests/bc-audit-probes/drive.py eval <sol> <Contract> '<expr1>' '<expr2>' ...
```

The generated contract is `importedContract`; probe fns called by name. Opens are
injected so short names work: `CheckedInput`, `CallTarget`, `CallResult`,
`Value`, `State`, `Examples` helpers.

### Getting our execution value (word or int)
Return type int* comes back as `Value.int N` (sign-extended 2^256 form for
negatives); uint*/bytes* as `Value.word N`. Extract raw:

```
'(toString (repr (CheckedInput.ownCall 32 importedContract (CallTarget.name "FN") State.empty [ARGS])))'
```
ARGS are `Value.word N` / `Value.int N`, comma-separated in `[...]`.

Or assert directly:
- `Examples.checkedOwnCallWordMatches 32 importedContract "FN" State.empty [ARGS] EXPECTED`  (only matches Value.word)
- `Examples.checkedOwnCallPanicMatches 32 importedContract "FN" State.empty [ARGS] 0x11`

### solc/Forge ground truth for VALUES
`accept`/`eval` solc line only tells accept/reject. For runtime VALUE ground
truth, either (a) hand-compute the EVM result (spec is unambiguous for arithmetic/
conversions) then confirm suspected divergences with Forge, or (b) write a Forge
test with a getter under a foundry project and run
`/Users/dan/.foundry/bin/forge test`.

## Classification
1. WRONG-VALUE (unsound): both accept, our value != solc/Forge value. Highest.
2. OVER-ACCEPT: we accept, solc rejects.
3. OVER-REJECT: we reject, solc accepts. Record, don't chase.
4. PARITY: match.
