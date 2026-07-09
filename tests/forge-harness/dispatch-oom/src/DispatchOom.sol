// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// External-dispatch OOM guard (D-OOM-DISPATCH #83) + try/catch success-return
// OOM propagation (TC-OOM1).
//
// An external entry with a `memory`-location dynamic reference parameter
// (`bytes memory`, `uint256[] memory`) decodes the calldata EAGERLY: solc runs
// `allocate_memory_array`, which panics 0x41 when the declared length exceeds
// `0xffffffffffffffff`, BEFORE the calldata data-presence bounds check.  A
// `calldata`-location parameter returns a pointer and never allocates, so an
// oversized length stays an empty/bounds `revert(0, 0)`.

interface DispatchOomReturner {
    function getBytes() external returns (bytes memory);
}

contract DispatchOom {
    // EAGER (memory) `bytes` param: oversized length -> Panic(0x41).
    function memBytesLength(bytes memory x) external pure returns (uint256) {
        return x.length;
    }

    // LAZY (calldata) `bytes` param: oversized length -> empty revert.
    function calldataBytesLength(bytes calldata y)
        external
        pure
        returns (uint256)
    {
        return y.length;
    }

    // EAGER (memory) `uint256[]` param: oversized length -> Panic(0x41).
    function memUintArrayLength(uint256[] memory a)
        external
        pure
        returns (uint256)
    {
        return a.length;
    }

    // LAZY (calldata) `uint256[]` param: oversized length -> empty revert.
    function calldataUintArrayLength(uint256[] calldata b)
        external
        pure
        returns (uint256)
    {
        return b.length;
    }

    // TC-OOM1: a SUCCESSFUL try-call whose returndata carries an oversized
    // dynamic length is decoded (allocated) in the success path -> Panic(0x41),
    // which is NOT caught (it is a fresh caller revert, not the callee's
    // returndata), so it propagates uncaught.  A genuinely-short returndata is
    // an empty decode revert (also uncaught).  The `catch` sentinel 0xdead is
    // returned only when the CALL itself fails.
    function tryBytesLength(address target) external returns (uint256) {
        try DispatchOomReturner(target).getBytes() returns (bytes memory b) {
            return b.length;
        } catch {
            return 0xdead;
        }
    }
}

// Returns raw returndata = offset(0x20) ++ length(2^64): an oversized dynamic
// `bytes` length.  (A `fallback ... returns (bytes memory)` sets the returndata
// to exactly these bytes, so it crafts the malformed encoding directly.)
contract DispatchOomReturnHuge {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(bytes32(uint256(0x20)), bytes32(uint256(2 ** 64)));
    }
}

// Returns raw returndata = offset(0x20) ++ length(1) with NO data byte: a
// genuinely-short (bounds-failing) encoding -> empty decode revert.
contract DispatchOomReturnShort {
    fallback(bytes calldata) external returns (bytes memory) {
        return bytes.concat(bytes32(uint256(0x20)), bytes32(uint256(1)));
    }
}
