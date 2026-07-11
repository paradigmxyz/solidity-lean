// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// TUPLE-VARDECL-FROM-ABI-DECODE (#171) — a multi-binding tuple variable
// DECLARATION whose initializer is `abi.decode(data, (T1, …, Tn))`. solc accepts
// these and binds each declared local to the corresponding decoded component;
// an omitted component (`(uint x, ) = abi.decode(...)`) is a skipped binding.
// solidity-lean accepted the contract but the source→core lowering returned
// `none` for the declaration-from-decode position (only the RETURN position and
// the tuple-ASSIGNMENT position were handled), so replay yielded
// `TypeError.unsupported`. The fix reuses the tuple-assignment lowering: declare
// the fresh locals, then bind the decoded components through `assignTuple`.
contract TupleVarDeclAbiDecodeTarget {
    // Value-only pair: both components declared.
    function addPair(bytes calldata data) external pure returns (uint256) {
        (uint256 x, uint256 y) = abi.decode(data, (uint256, uint256));
        return x + y;
    }

    // Omitted trailing component (a hole binding): only `x` is declared.
    function firstOfPair(bytes calldata data) external pure returns (uint256) {
        (uint256 x, ) = abi.decode(data, (uint256, uint256));
        return x;
    }

    // Omitted leading component: only `y` is declared.
    function secondOfPair(bytes calldata data) external pure returns (uint256) {
        (, uint256 y) = abi.decode(data, (uint256, uint256));
        return y;
    }

    // Reference-type component: a dynamic `uint256[]` is decoded alongside a
    // value component. Returns the value head and the array's second element.
    function headAndArray(bytes calldata data)
        external
        pure
        returns (uint256, uint256)
    {
        (uint256 x, uint256[] memory a) = abi.decode(data, (uint256, uint256[]));
        return (x, a[1]);
    }
}
