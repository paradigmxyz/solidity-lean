// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// LIT-COERCION FAMILY (#141-#145): a string/hex/bytes LITERAL flowing into a
// declared fixed `bytesN` target through a target-BLIND lowering path must be
// coerced by solc to the fixed target — ONE left-aligned 32-byte word (the
// <= n meaningful bytes at the top, zero-padded). Covers: emit event data and
// indexed topic (#141), custom-error revert / require data (#141), dynamic
// array `.push` element (#142), `abi.encodeWithSelector` bare 4-byte hex
// selector literal (#143), external function-pointer value call arg (#144), and
// a `bytesN`-keyed mapping key (#145). Controls: a literal into a DYNAMIC
// `bytes` event field stays dynamic, and a NON-literal `bytes2` variable arg is
// byte-identical to the coerced literal.

contract LitCoercionFamily {
    event EvData(bytes2 x);
    event EvIdx(bytes2 indexed x);
    event EvDyn(bytes x);
    error Bad(bytes2 x);

    bytes2[] public arr;
    mapping(bytes4 => uint256) public m;

    // #141 emit: hex literal -> bytes2 event field, non-indexed data word.
    function emitData() external {
        emit EvData(hex"1234");
    }

    // #141 emit: hex literal -> bytes2 INDEXED event field, topic word (unhashed).
    function emitIdx() external {
        emit EvIdx(hex"1234");
    }

    // #141 revert: hex literal -> bytes2 custom-error parameter, one data word.
    function doRevert() external pure {
        revert Bad(hex"1234");
    }

    // #141 require: hex literal -> bytes2 custom-error parameter, one data word.
    function doRequire() external pure {
        require(false, Bad(hex"1234"));
    }

    // #142 push: hex literal -> bytes2 dynamic-array element, left-aligned word.
    function pushLit() external {
        arr.push(hex"1234");
    }

    // #145 mapping key: string literal -> bytes4 mapping key, masked & hashed.
    function setMap() external {
        m["abcd"] = 7;
    }

    // #143 encodeWithSelector: bare 4-byte HEX NUMBER literal selector accepted.
    function selData() external pure returns (bytes memory) {
        return abi.encodeWithSelector(0x12345678, uint256(7));
    }

    // CONTROL: literal -> DYNAMIC bytes event field stays dynamic (no coercion).
    function emitDyn() external {
        emit EvDyn(hex"1234");
    }

    // CONTROL: NON-literal bytes2 variable arg -> byte-identical to the literal.
    function emitVar(bytes2 v) external {
        emit EvData(v);
    }
}

contract LitPtrTarget {
    function g(bytes4 z) external pure returns (bytes4) {
        return z;
    }
}

contract LitPtrCaller {
    // #144 external function-pointer value call: string literal -> bytes4 param,
    // ABI-encoded as one left-aligned word in the call's calldata.
    function callPtr(address t) external returns (bytes4) {
        function(bytes4) external returns (bytes4) fn = LitPtrTarget(t).g;
        return fn("abcd");
    }
}
