# acc-pair: UniswapV2Pair (v2-core 6a9e7c9 plus the solar port patch), outside the envelope

Verdict: BLOCKED: external call (15x, first line 45: .call on an address); imports (7x, first line 3: the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)); inheritance (1x, first line 11: UniswapV2Pair inherits; only one contract with no bases); ABI types (6x, first DOMAIN_SEPARATOR(): only uintN, intN, bool, address and enum parameters and results)
Driver exit (strict tier exit): 3 (not certified)
Status: BLOCKED


| Field | Value |
| --- | --- |
| Driver scripts commit / tree | 20a27f39685284bea5a0fe40a7fed0437cfcf694 / 4904ff637c346c81e0bd2f6d858411c264c0aca3 |
| solar binary sha256 | None |
| solar binary built from | abe16b2ea8648505fda4d2f40416c748bd21a931 (tree defe9f13eeefd078ddfa18e12b0211eec0edd5f6); Rust sources equal to the driver commit: True |
| solidity-lean base argument | None |
| solidity-lean executed | None (parent -) |
| Options | -Ogas --evm-version osaka |
| Requested tier | certified |
| Source | sha256 444b8d56a805942d021dceb13f7d66393a8e6d61ea49ed75a67f498b1886a09b |
| Spec | natspec, sha256 444b8d56a805942d021dceb13f7d66393a8e6d61ea49ed75a67f498b1886a09b |
| solc | 0.8.35, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| Lean toolchain | None |
| Runtime bytecode sha256 | None |
| Gas bound | None |
| Strict tier | (not reached) |
| Blocked | [{"feature": "imports", "where": "line 3", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "imports", "where": "line 4", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "imports", "where": "line 5", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "imports", "where": "line 6", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "imports", "where": "line 7", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "imports", "where": "line 8", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "imports", "where": "line 9", "detail": "the source imports other files; the driver takes one self-contained file and never flattens (a frozen import closure is not supported yet)"}, {"feature": "inheritance", "where": "line 11", "detail": "UniswapV2Pair inherits; only one contract with no bases"}, {"feature": "external call", "where": "line 45", "detail": ".call on an address"}, {"feature": "external call", "where": "line 95", "detail": "a call of an external function (function () view external returns (address))"}, {"feature": "external call", "where": "line 117", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 118", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 143", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 144", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 155", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 156", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 177", "detail": "a call of an external function (function (address,uint256,uint256,bytes memory) external)"}, {"feature": "external call", "where": "line 178", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 179", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 198", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 199", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 204", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "external call", "where": "line 204", "detail": "a call of an external function (function (address) view external returns (uint256))"}, {"feature": "ABI types", "where": "", "detail": "DOMAIN_SEPARATOR(): only uintN, intN, bool, address and enum parameters and results"}, {"feature": "ABI types", "where": "", "detail": "PERMIT_TYPEHASH(): only uintN, intN, bool, address and enum parameters and results"}, {"feature": "ABI types", "where": "", "detail": "name(): only uintN, intN, bool, address and enum parameters and results"}, {"feature": "ABI types", "where": "", "detail": "permit(address,address,uint256,uint256,uint8,bytes32,bytes32): only uintN, intN, bool, address and enum parameters and results"}, {"feature": "ABI types", "where": "", "detail": "swap(uint256,uint256,address,bytes): only uintN, intN, bool, address and enum parameters and results"}, {"feature": "ABI types", "where": "", "detail": "symbol(): only uintN, intN, bool, address and enum parameters and results"}] |
| Replay | (not reached) |
| Host peak used memory (all processes) | 603 MiB of 14531 |
| Peak tree RSS / largest process | 1 / 32 MiB |
| Wall seconds | 0.3 |

Final statement: (not built)

Final check: (not reached)

Closure: (not reached)

Files: record.json (its run_files lists the driver's own files), certify.log, inputs/ (what the driver
committed before the proof run), generated/ (every file of the run's Certified/<name>/ as the build saw it),
provenance.json, receipt.json, driver.log, and MANIFEST.sha256, the sha256 of every file here but itself.
