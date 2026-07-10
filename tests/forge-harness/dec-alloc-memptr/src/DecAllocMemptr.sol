// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// DEC-ALLOC-MEMPTR (#114): the memory-allocation guard on an EAGER (memory)
// dynamic reference decode target must include solc's running free-memory
// pointer term.
//
// `finalize_allocation` (YulUtilFunctions.cpp:3256) panics 0x41 when
// `newFreePtr := add(memPtr, roundUp(size)) > 0xffffffffffffffff`, where memPtr
// is the CURRENT free-memory pointer (>= 0x80). At the external-dispatch decode
// of the first/only dynamic reference parameter, memPtr is still its 0x80 reset.
// So there is a band of lengths BELOW the raw `elementSize * n + 0x20 > 2^64-1`
// bound where solc still panics because the 0x80 base tips `newFreePtr` over
// 2^64-1. `arrayAllocationSizeFunction` also rounds a BYTE length UP to a word
// (`size := roundUp(length)`), widening the byte-array band further.
//
// These entries carry, in calldata, an array/byte length inside that band:
// solc's decoder allocates BEFORE the calldata data-presence check
// (ABIFunctions.cpp:1184), so the finalize panic fires as pure arithmetic (no
// memory expansion, no out-of-gas) -> a deterministic Panic(0x41). The LAZY
// (calldata) counterparts never allocate, so the same length stays the empty
// bounds `revert(0, 0)`.

contract DecAllocMemptr {
    // EAGER (memory) `uint256[]` param. Band length -> Panic(0x41) via the
    // memPtr term (raw `32*n + 32` alone would NOT overflow 2^64-1).
    function memUintArrayLength(uint256[] memory a)
        external
        pure
        returns (uint256)
    {
        return a.length;
    }

    // LAZY (calldata) `uint256[]` param: no allocation -> empty revert.
    function calldataUintArrayLength(uint256[] calldata b)
        external
        pure
        returns (uint256)
    {
        return b.length;
    }

    // EAGER (memory) `bytes` param. Band length near 2^64 -> Panic(0x41) via the
    // byte-length roundUp-to-a-word + memPtr terms (raw `n + 32` would NOT
    // overflow 2^64-1).
    function memBytesLength(bytes memory x)
        external
        pure
        returns (uint256)
    {
        return x.length;
    }

    // LAZY (calldata) `bytes` param: no allocation -> empty revert.
    function calldataBytesLength(bytes calldata y)
        external
        pure
        returns (uint256)
    {
        return y.length;
    }
}
