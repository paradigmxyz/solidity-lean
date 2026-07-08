// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// V1 divergence lane: a calldata slice `a[i:j]` whose bounds are out of range
// (`i > j` or `j > a.length`) reverts with EMPTY returndata (`revert(0, 0)`) in
// solc's default (non-debug) mode — YulUtilFunctions.cpp:2523-2539 slice bounds
// check routes to revertReasonIfDebugBody (:4598-4605). A regular array/bytes
// INDEX access `a[k]` out of range still panics 0x32 (a different Yul helper).
contract CalldataSliceOobHarnessTarget {
    // Dynamic-bounds calldata slice: OOB bounds -> empty revert; in-bounds -> value.
    function slice(bytes calldata input, uint256 start, uint256 stop)
        external
        pure
        returns (bytes memory)
    {
        return input[start:stop];
    }

    // Regular calldata byte INDEX access: out-of-range k -> Panic(0x32) (unchanged).
    function indexAt(bytes calldata input, uint256 k)
        external
        pure
        returns (bytes1)
    {
        return input[k];
    }
}
